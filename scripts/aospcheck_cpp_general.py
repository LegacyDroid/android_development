#!/usr/bin/env python3
"""
aospcheck_cpp_general.py

Dedicated AOSP syntax and diagnostic checker for C, C++, and Headers.
Combines compilation database token-level sanitization, 17-pattern header
content sniffing, standard AOSP Bionic include heuristics, Clang warning tag
attribution, and graceful process management.

Exit codes:
  0 = Clean
  1 = Errors present
  2 = Warnings only (--werror or --fail-on-warning)
  3 = Usage / tool error
  130 = Interrupted
"""

from __future__ import annotations

import argparse
import fnmatch
import glob as globmod
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import threading
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Set

VERSION = "2.1.0-cpp"

EXIT_OK, EXIT_ERRORS, EXIT_WARNINGS, EXIT_USAGE, EXIT_INTERRUPT = 0, 1, 2, 3, 130

C_SOURCE_EXTS = {".c"}
CPP_SOURCE_EXTS = {".cpp", ".cc", ".cxx", ".c++", ".C"}
HEADER_EXTS = {".h", ".hpp", ".hh", ".hxx", ".h++"}
ALL_CPP_EXTS = C_SOURCE_EXTS | CPP_SOURCE_EXTS | HEADER_EXTS

SKIP_DIRS = {".git", ".repo", ".svn", ".idea", "out", "__pycache__"}
MODULE_MARKERS = ("Android.bp", "Android.mk", "Kbuild")

CLANG_DIAG_RE = re.compile(
    r"^(?P<file>(?:[A-Za-z]:[\\/])?.+?):(?P<line>\d+):(?P<col>\d+):\s*"
    r"(?P<sev>fatal error|error|warning|note):\s+(?P<msg>.*)$",
    re.IGNORECASE,
)

CLANG_CONTEXT_RES = [
    re.compile(r"file not found", re.I),
    re.compile(r"use of undeclared identifier", re.I),
    re.compile(r"unknown type name", re.I),
    re.compile(r"no member named", re.I),
    re.compile(r"no template named", re.I),
    re.compile(r"no function template named", re.I),
]

_CPP_TOKEN_RES = (
    re.compile(r"\bnamespace\s+[\w:]"),
    re.compile(r"\bnamespace\s*\{"),
    re.compile(r"\btemplate\s*<"),
    re.compile(r"\bclass\s+\w+\s*[{;:]"),
    re.compile(r"\bstruct\s+\w+\s*:\s*(public|protected|private)\b"),
    re.compile(r"\bstd\s*::"),
    re.compile(r"\b\w+::\w+"),
    re.compile(r"\busing\s+namespace\b"),
    re.compile(r"\boperator\s*[^\w\s]"),
    re.compile(r"\b(public|private|protected)\s*:"),
    re.compile(r"\btry\s*\{"),
    re.compile(r"\bcatch\s*\("),
    re.compile(r"\bnoexcept\b"),
    re.compile(r"\bconstexpr\b"),
    re.compile(r"\bnullptr\b"),
    re.compile(
        r"#\s*include\s*<(vector|string|map|set|multimap|multiset|"
        r"unordered_map|unordered_set|memory|algorithm|functional|utility|"
        r"array|tuple|pair|atomic|thread|mutex|condition_variable|chrono|"
        r"iostream|sstream|fstream|istream|ostream|stdexcept|type_traits|"
        r"bitset|deque|list|queue|stack|regex|random|forward_list|optional|"
        r"variant|string_view|span|cstdint|cstddef|cstdio|cstring|cstdlib|cmath)>"
    ),
)


class C:
    RESET = "\033[0m"
    BOLD = "\033[1m"
    DIM = "\033[2m"
    RED = "\033[1;31m"
    GREEN = "\033[32m"
    YELLOW = "\033[33m"
    MAGENTA = "\033[35m"
    CYAN = "\033[36m"


def colorize(s: str, code: str, on: bool) -> str:
    return f"{code}{s}{C.RESET}" if on else s


@dataclass
class Diagnostic:
    file: str
    line: int
    col: int
    severity: str
    tool: str
    message: str
    tag: str = ""

    _RANK = {"error": 0, "warning": 1, "context": 2, "note": 3}

    def sort_key(self):
        return (self.file, self.line, self.col, self._RANK.get(self.severity, 9))


class ProcessRegistry:
    def __init__(self):
        self._lock = threading.Lock()
        self._procs = set()

    def add(self, proc):
        with self._lock:
            self._procs.add(proc)

    def discard(self, proc):
        with self._lock:
            self._procs.discard(proc)

    def kill_all(self):
        with self._lock:
            procs = list(self._procs)
        for p in procs:
            try:
                if p.poll() is None:
                    p.terminate()
            except OSError:
                pass
        time.sleep(0.15)
        for p in procs:
            try:
                if p.poll() is None:
                    p.kill()
            except OSError:
                pass


PROC_REGISTRY = ProcessRegistry()


def host_tag() -> str:
    if sys.platform.startswith("linux"):
        return "linux-x86"
    if sys.platform == "darwin":
        return "darwin-x86"
    if sys.platform.startswith("win"):
        return "windows-x86"
    return "linux-x86"


def find_aosp_root(explicit: Optional[str], inputs: List[str]) -> Optional[Path]:
    cands: List[Path] = []
    if explicit:
        cands.append(Path(explicit).expanduser().resolve())
    if os.environ.get("ANDROID_BUILD_TOP"):
        cands.append(Path(os.environ["ANDROID_BUILD_TOP"]).expanduser().resolve())
    cands.append(Path.cwd())
    for item in inputs[:8]:
        try:
            cands.append(Path(item).expanduser().resolve().parent)
        except Exception:
            pass
    for c in cands:
        if not c.is_dir():
            continue
        for up in [c, *c.parents]:
            if (up / "build/soong/soong_ui.bash").is_file() or (up / "build/envsetup.sh").is_file():
                return up
    return None


def find_aosp_clang(root: Optional[Path], exe_name: str) -> Optional[Path]:
    if not root:
        return None
    base = root / "prebuilts/clang/host" / host_tag()
    if not base.is_dir():
        return None
    candidates = []
    for d in base.iterdir():
        if d.is_dir() and d.name.startswith("clang-"):
            m = re.search(r"clang-r(\d+)", d.name)
            rev = int(m.group(1)) if m else 0
            candidates.append((rev, d))
    candidates.sort(key=lambda x: x[0], reverse=True)
    for _, d in candidates:
        cand = d / "bin" / (exe_name + (".exe" if os.name == "nt" else ""))
        if cand.is_file():
            return cand
    return None


def sniff_is_cpp_header(path: Path) -> bool:
    try:
        raw = path.read_bytes()[:65536]
        text = raw.decode("utf-8", errors="replace")
        return any(rx.search(text) for rx in _CPP_TOKEN_RES)
    except Exception:
        return False


def aosp_default_include_dirs(root: Optional[Path]) -> List[str]:
    if not root:
        return []
    subdirs = [
        "bionic/libc/include",
        "bionic/libc/kernel/uapi",
        "bionic/libc/kernel/uapi/asm-generic",
        "system/core/include",
        "system/core/base/include",
        "system/core/libutils/include",
        "system/core/liblog/include",
        "system/core/libcutils/include",
        "system/libbase/include",
        "frameworks/native/include",
        "hardware/libhardware/include",
    ]
    return [str(root / s) for s in subdirs if (root / s).is_dir()]


def walk_include_flags(abs_file: Path, aosp_root: Optional[Path]) -> List[str]:
    here = abs_file.parent
    module_root = None
    cur = here
    for _ in range(12):
        if any((cur / m).exists() for m in MODULE_MARKERS):
            module_root = cur
            break
        if aosp_root and cur == aosp_root:
            module_root = cur
            break
        if cur.parent == cur:
            break
        cur = cur.parent

    chain = []
    c = here
    while True:
        chain.append(c)
        if module_root and c == module_root:
            break
        if c.parent == c:
            break
        c = c.parent

    flags = []
    for d in chain:
        for cand in (d, d / "include"):
            if cand.is_dir():
                flags.extend(["-I", str(cand)])
    return flags


# Flags to strip outright from CDB commands
DB_STRIP_BOOL = {"-c", "-S", "-E", "-MMD", "-MD", "-MP", "-MM", "-M", "-MG"}
DB_STRIP_VALUED = {"-o", "-MF", "-MT", "-MQ", "--serialize-diagnostics", "--dependency-file"}
DB_VALUED_PASS = {
    "-I", "-isystem", "-iquote", "-idirafter", "-include", "-imacros", "-include-pch",
    "-D", "-U", "-x", "-mllvm", "-Xclang", "-Xpreprocessor", "-isysroot", "-sysroot",
    "-iframework", "-ivfsoverlay", "-target", "--target", "-arch", "-gcc-toolchain",
}
DB_COMPILERS = {"clang", "clang++", "gcc", "g++", "cc", "c++"}


def sanitize_cdb_command(entry: dict, fallback_root: Optional[Path]) -> Tuple[List[str], str]:
    directory = entry.get("directory") or (str(fallback_root) if fallback_root else os.getcwd())
    raw_tokens = entry.get("arguments")
    if raw_tokens is None:
        raw_tokens = shlex.split(entry.get("command") or "")
    if not raw_tokens:
        return [], directory

    file_target = str((Path(directory) / entry["file"]).resolve()) if "file" in entry else ""
    cmd_prefix = [raw_tokens[0]]
    flags: List[str] = []
    inputs: List[str] = []
    i, n = 1, len(raw_tokens)

    while i < n:
        t = raw_tokens[i]
        if t in DB_STRIP_BOOL:
            i += 1
            continue
        if t in DB_STRIP_VALUED:
            i += 2
            continue
        if t in DB_VALUED_PASS:
            flags.append(t)
            if i + 1 < n:
                flags.append(raw_tokens[i + 1])
            i += 2
            continue
        if t.startswith("-o") and len(t) > 2 and not t.startswith("-O"):
            i += 1
            continue
        if t.startswith(("-MF", "-MT", "-MQ")) and len(t) > 2:
            i += 1
            continue
        if t.startswith("-"):
            flags.append(t)
            i += 1
            continue
        if not flags and not inputs and os.path.basename(t) in DB_COMPILERS:
            cmd_prefix.append(t)
            i += 1
            continue
        try:
            if str((Path(directory) / t).resolve()) == file_target:
                inputs.append(t)
                i += 1
                continue
        except Exception:
            pass
        i += 1

    if "-fsyntax-only" not in flags:
        flags.insert(0, "-fsyntax-only")
    if not inputs and "file" in entry:
        inputs.append(entry["file"])

    return cmd_prefix + flags + inputs, directory


def parse_clang_output(raw: str, strict_context: bool) -> List[Diagnostic]:
    diags = []
    for line in raw.splitlines():
        line = line.rstrip()
        m = CLANG_DIAG_RE.match(line)
        if not m:
            continue
        sev = m.group("sev").lower()
        if sev == "fatal error":
            sev = "error"
        msg = m.group("msg").strip()
        tag = ""
        tm = re.search(r"\s*\[(-W[^\]\s]+)\]$", msg)
        if tm:
            tag = tm.group(1)
            msg = msg[: tm.start()]

        if sev == "error" and not strict_context:
            if any(rx.search(msg) for rx in CLANG_CONTEXT_RES):
                sev = "context"

        diags.append(Diagnostic(
            file=m.group("file"),
            line=int(m.group("line")),
            col=int(m.group("col")),
            severity=sev,
            tool="clang",
            message=msg,
            tag=tag,
        ))
    return diags


def run_clang_file(
    path: Path,
    cdb_entry: Optional[dict],
    args: argparse.Namespace,
    root: Optional[Path],
    clang_exe: Path,
    clangxx_exe: Path,
    env: dict,
) -> Tuple[List[Diagnostic], float, Optional[int]]:
    t0 = time.time()
    ext = path.suffix.lower()
    is_header = ext in HEADER_EXTS
    is_cpp = ext in CPP_SOURCE_EXTS or (is_header and sniff_is_cpp_header(path))

    if cdb_entry:
        cmd, cwd = sanitize_cdb_command(cdb_entry, root)
    else:
        cwd = str(root) if root else None
        exe = str(clangxx_exe if is_cpp else clang_exe)
        cmd = [exe, "-fsyntax-only", f"-std={args.cpp_std if is_cpp else args.c_std}"]
        if is_header:
            cmd.extend(["-x", "c++-header" if is_cpp else "c-header"])
        cmd.extend([
            "-Wall", "-Wextra", "-Wdate-time", "-Wthread-safety",
            "-Wno-unknown-warning-option", "-Wno-unused-parameter",
            "-Wno-nullability-completeness",
        ])
        if args.android_defines:
            cmd.extend(["-D__ANDROID__", "-DANDROID"])
        if args.aosp_default_includes and root:
            for inc in aosp_default_include_dirs(root):
                cmd.extend(["-I", inc])
        cmd.extend(walk_include_flags(path, root))
        for inc in args.includes:
            cmd.extend(["-I", inc])
        for d in args.defines:
            cmd.extend(["-D", d])
        cmd.extend(args.cflag)
        cmd.append(str(path))

    try:
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=cwd, env=env)
    except Exception as e:
        return [Diagnostic(str(path), 0, 0, "error", "clang", str(e))], time.time() - t0, 1

    PROC_REGISTRY.add(proc)
    try:
        out_b, err_b = proc.communicate(timeout=args.timeout if args.timeout > 0 else None)
        raw = (err_b or b"").decode("utf-8", "replace") + (out_b or b"").decode("utf-8", "replace")
        diags = parse_clang_output(raw, args.strict_context)
        return diags, time.time() - t0, proc.returncode
    except subprocess.TimeoutExpired:
        try:
            proc.kill()
        except OSError:
            pass
        return [Diagnostic(str(path), 0, 0, "error", "clang", f"Timeout after {args.timeout}s")], time.time() - t0, 124
    finally:
        PROC_REGISTRY.discard(proc)


def build_argparser():
    ap = argparse.ArgumentParser(
        prog="aospcheck_cpp_general.py",
        description="AOSP C, C++ & Header Syntax / Diagnostic Checker",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("-i", "--input", action="append", required=True, help="File, dir, or glob. Repeatable.")
    ap.add_argument("-j", "--jobs", type=int, default=os.cpu_count() or 4, help="Worker threads.")
    ap.add_argument("--compile-commands", help="Path to compile_commands.json database.")
    ap.add_argument("--aosp-root", help="AOSP Root directory.")
    ap.add_argument("--clang", help="Explicit clang compiler path.")
    ap.add_argument("--clangxx", help="Explicit clang++ compiler path.")
    ap.add_argument("--c-std", default="gnu17", help="C standard dialect (Default: gnu17).")
    ap.add_argument("--cpp-std", default="gnu++17", help="C++ standard dialect (Default: gnu++17).")
    ap.add_argument("-I", "--include", dest="includes", action="append", default=[], help="Extra -I dir. Repeatable.")
    ap.add_argument("-D", "--define", dest="defines", action="append", default=[], help="Extra -D define. Repeatable.")
    ap.add_argument("--cflag", action="append", default=[], help="Extra compiler flag. Repeatable.")
    ap.add_argument("--no-headers", action="store_true", help="Skip header files.")
    ap.add_argument("--no-android-defines", dest="android_defines", action="store_false", default=True, help="Disable default __ANDROID__ define.")
    ap.add_argument("--no-aosp-default-includes", dest="aosp_default_includes", action="store_false", default=True, help="Disable Bionic fallback includes.")
    ap.add_argument("--strict-context", action="store_true", help="Treat missing headers/symbols as real errors.")
    ap.add_argument("--hide-context", action="store_true", help="Hide missing dependency/symbol diagnostics.")
    ap.add_argument("-Werror", "--werror", action="store_true", help="Treat warnings as errors.")
    ap.add_argument("--timeout", type=float, default=120.0, help="Timeout per file in seconds.")
    ap.add_argument("--json", help="Write JSON report to file.")
    ap.add_argument("-q", "--quiet", action="store_true", help="Suppress progress and banners.")
    ap.add_argument("--color", choices=["auto", "always", "never"], default="auto")
    return ap


def main(argv=None) -> int:
    args = build_argparser().parse_args(argv)
    color_on = sys.stdout.isatty() if args.color == "auto" else (args.color == "always")

    root = find_aosp_root(args.aosp_root, args.input)
    clang_bin = Path(args.clang) if args.clang else (find_aosp_clang(root, "clang") or shutil.which("clang"))
    clangxx_bin = Path(args.clangxx) if args.clangxx else (find_aosp_clang(root, "clang++") or shutil.which("clang++"))

    if not clang_bin or not clangxx_bin:
        print("Clang toolchain not found. Set --clang / --clangxx or --aosp-root.", file=sys.stderr)
        return EXIT_USAGE

    clang_bin = Path(clang_bin)
    clangxx_bin = Path(clangxx_bin)

    cdb = {}
    if args.compile_commands:
        cdb_path = Path(args.compile_commands).expanduser()
        if cdb_path.is_dir():
            cdb_path = cdb_path / "compile_commands.json"
        if cdb_path.is_file():
            try:
                entries = json.loads(cdb_path.read_text(encoding="utf-8"))
                for entry in entries:
                    d = entry.get("directory", "")
                    f = entry.get("file", "")
                    if f:
                        ap = str((Path(d) / f).resolve())
                        cdb[ap] = entry
            except Exception as e:
                print(f"Failed to parse compile_commands.json: {e}", file=sys.stderr)
                return EXIT_USAGE

    all_files: List[Path] = []
    target_exts = set(ALL_CPP_EXTS)
    if args.no_headers:
        target_exts -= HEADER_EXTS

    for item in args.input:
        if globmod.has_magic(item):
            for m in globmod.glob(item, recursive=True):
                p = Path(m).resolve()
                if p.is_file() and p.suffix.lower() in target_exts:
                    all_files.append(p)
        else:
            p = Path(item).resolve()
            if p.is_dir():
                for r, dirs, files in os.walk(p):
                    dirs[:] = [d for d in dirs if d not in SKIP_DIRS and not d.startswith(".")]
                    for f in files:
                        fp = Path(r) / f
                        if fp.suffix.lower() in target_exts:
                            all_files.append(fp)
            elif p.is_file() and p.suffix.lower() in target_exts:
                all_files.append(p)

    all_files = sorted(set(all_files))
    if not all_files:
        print("No supported C, C++, or Header files found.", file=sys.stderr)
        return EXIT_USAGE

    env = dict(os.environ)
    env["LC_ALL"] = "C"

    if not args.quiet:
        print(colorize(f"aospcheck_cpp {VERSION} — Checking {len(all_files)} files", C.BOLD, color_on))
        print(f"  AOSP Root : {root or '(Not detected)'}")
        print(f"  Clang     : {clang_bin}")
        print(f"  CDB Match : {len(cdb)} entries loaded")

    results: Dict[str, Tuple[List[Diagnostic], float]] = {}
    done = 0
    t0 = time.time()

    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as ex:
        futs = {
            ex.submit(run_clang_file, p, cdb.get(str(p)), args, root, clang_bin, clangxx_bin, env): p
            for p in all_files
        }
        try:
            for fut in as_completed(futs):
                p = futs[fut]
                diags, dur, rc = fut.result()
                results[str(p)] = (diags, dur)
                done += 1
                if sys.stderr.isatty() and not args.quiet:
                    sys.stderr.write(f"\r\x1b[K  [{done}/{len(all_files)}] checked")
                    sys.stderr.flush()
        except KeyboardInterrupt:
            sys.stderr.write("\nInterrupted! Terminating compiler child processes...\n")
            PROC_REGISTRY.kill_all()
            return EXIT_INTERRUPT

    if sys.stderr.isatty() and not args.quiet:
        sys.stderr.write("\n")

    elapsed = time.time() - t0
    flat_diags: List[Diagnostic] = []
    for diags, _ in results.values():
        flat_diags.extend(diags)

    if args.werror:
        for d in flat_diags:
            if d.severity == "warning":
                d.severity = "error"

    if args.hide_context:
        flat_diags = [d for d in flat_diags if d.severity != "context"]

    cur_file = None
    for d in sorted(flat_diags, key=Diagnostic.sort_key):
        if d.file != cur_file:
            cur_file = d.file
            print(colorize(f"\n-- {d.file or '<compiler>'} " + "-" * 45, C.DIM, color_on))
        sev_color = C.RED if d.severity == "error" else (C.YELLOW if d.severity == "warning" else C.MAGENTA)
        tag_str = f" [{d.tag}]" if d.tag else ""
        print(f"{d.file}:{d.line}:{d.col}: {colorize(d.severity.upper(), sev_color, color_on)}{tag_str} {d.message}")

    counts = Counter(d.severity for d in flat_diags)
    print(colorize("\n" + "=" * 60, C.DIM, color_on))
    print(f"Checked {len(all_files)} files in {elapsed:.2f}s")
    print(f"Errors   : {colorize(str(counts['error']), C.RED, color_on)}")
    print(f"Warnings : {colorize(str(counts['warning']), C.YELLOW, color_on)}")
    print(f"Context  : {colorize(str(counts['context']), C.MAGENTA, color_on)} (Missing headers / stubs)")

    if args.json:
        payload = {
            "version": VERSION,
            "elapsed_sec": round(elapsed, 2),
            "summary": dict(counts),
            "diagnostics": [asdict(d) for d in sorted(flat_diags, key=Diagnostic.sort_key)],
        }
        Path(args.json).write_text(json.dumps(payload, indent=2), encoding="utf-8")
        print(f"Report saved to {args.json}")

    return EXIT_ERRORS if counts["error"] > 0 else (EXIT_WARNINGS if counts["warning"] > 0 else EXIT_OK)


if __name__ == "__main__":
    sys.exit(main())
