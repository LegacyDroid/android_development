#!/usr/bin/env python3
"""
aospcheck_java_general.py

Dedicated AOSP syntax and diagnostic checker for Java and Kotlin.
Combines package-aware batching, auto sourcepath deduction, context-triage,
caret-accurate column parsing, and graceful process management.

Exit codes:
  0 = Clean
  1 = Errors present
  2 = Warnings only
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
import tempfile
import threading
import time
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field, asdict, replace
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Set

VERSION = "2.1.0-java"

EXIT_OK, EXIT_ERRORS, EXIT_WARNINGS, EXIT_USAGE, EXIT_INTERRUPT = 0, 1, 2, 3, 130

JAVA_EXTS = {".java"}
KOTLIN_EXTS = {".kt"}
SUPPORTED_EXTS = JAVA_EXTS | KOTLIN_EXTS
SKIP_DIRS = {".git", ".repo", ".svn", ".idea", "out", "__pycache__", ".gradle"}

JAVA_DIAG_RE = re.compile(
    r"^(?P<file>(?:[A-Za-z]:[\\/])?.+?):(?P<line>\d+):(?:(?P<col>\d+):)? "
    r"(?P<severity>warning|error|Note): (?P<message>.*)$",
    re.IGNORECASE,
)
JAVAC_CARET_RE = re.compile(r"^(\s*)\^")

KOTLIN_DIAG_RE = re.compile(
    r"^(?P<file>(?:[A-Za-z]:[\\/])?.+?):(?P<line>\d+):(?P<col>\d+):\s*"
    r"(?P<severity>warning|error):\s*(?P<message>.*)$",
    re.IGNORECASE,
)
KOTLIN_EW_DIAG_RE = re.compile(
    r"^(?P<severity>[ew]): (?:file://)?(?P<file>(?:[A-Za-z]:[\\/])?.+?):"
    r"(?P<line>\d+):(?P<col>\d+):\s*(?P<message>.*)$",
    re.IGNORECASE,
)

PACKAGE_LINE_RE = re.compile(r"^\s*package\s+([A-Za-z_][A-Za-z0-9_.]*)\s*;?", re.IGNORECASE)

JAVA_CONTEXT_RES = [
    re.compile(r"^cannot find symbol", re.I),
    re.compile(r"^package \S+ does not exist", re.I),
    re.compile(r"^cannot access ", re.I),
    re.compile(r"^class file for \S+ not found", re.I),
    re.compile(r"^bad symbolic reference", re.I),
    re.compile(r"file not found", re.I),
]

KOTLIN_CONTEXT_RES = [
    re.compile(r"unresolved reference", re.I),
    re.compile(r"unresolved import", re.I),
    re.compile(r"cannot access", re.I),
    re.compile(r"file not found", re.I),
]


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
    severity: str  # error | warning | note | context
    tool: str
    message: str
    tag: str = ""

    _RANK = {"error": 0, "warning": 1, "context": 2, "note": 3}

    def sort_key(self):
        return (self.file, self.line, self.col, self._RANK.get(self.severity, 9))


@dataclass
class SourceFile:
    path: Path
    lang: str
    package: Optional[str] = None


@dataclass
class BatchTask:
    lang: str
    files: List[SourceFile]
    label: str


@dataclass
class TaskResult:
    task: BatchTask
    diags: List[Diagnostic] = field(default_factory=list)
    raw: str = ""
    cmd: List[str] = field(default_factory=list)
    rc: Optional[int] = None
    duration: float = 0.0


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
            if (up / "build" / "soong" / "soong_ui.bash").is_file() or (
                up / "build" / "envsetup.sh"
            ).is_file():
                return up
    return None


def find_javac(root: Optional[Path], override: Optional[str]) -> Tuple[Optional[Path], Optional[Path]]:
    if override:
        p = Path(override).expanduser()
        if p.is_file():
            return p, p.parent.parent
        if p.is_dir():
            exe = p / ("javac.exe" if os.name == "nt" else "javac")
            return (exe, p) if exe.is_file() else (None, None)
        return None, None

    if root:
        candidates = []

        android_java_home = os.environ.get("ANDROID_JAVA_HOME")
        if android_java_home:
            home = Path(android_java_home).expanduser()
            exe = home / "bin" / ("javac.exe" if os.name == "nt" else "javac")
            if exe.is_file():
                candidates.append((0, 0, 0, exe))

        base = root / "prebuilts" / "jdk"
        if base.is_dir():
            for jd in base.iterdir():
                if not jd.is_dir():
                    continue
                match = re.fullmatch(r"jdk(\d+)", jd.name)
                version = int(match.group(1)) if match else 0
                jdk_preference = 0 if jd.name == "jdk17" else 1
                for exe in jd.glob(
                    f"*/bin/{'javac.exe' if os.name == 'nt' else 'javac'}"
                ):
                    if exe.is_file():
                        host_preference = 0 if exe.parent.parent.name == host_tag() else 1
                        candidates.append((jdk_preference, host_preference, -version, exe))

        for _, _, _, exe in sorted(
            candidates, key=lambda item: (item[0], item[1], item[2], str(item[3]))
        ):
            return exe, exe.parent.parent

    w = shutil.which("javac")
    return (Path(w), None) if w else (None, None)


def find_kotlinc(root: Optional[Path], override: Optional[str]) -> Optional[Path]:
    if override:
        p = Path(override).expanduser()
        return p if p.is_file() else None
    if root:
        patterns = (
            "prebuilts/sdk/current/kotlinc/bin/kotlinc*",
            "prebuilts/sdk/*/kotlinc/bin/kotlinc*",
            "external/kotlinc/bin/kotlinc*",
            f"prebuilts/build-tools/{host_tag()}/bin/kotlinc*",
        )
        for pat in patterns:
            for cand in root.glob(pat):
                if cand.is_file() and not cand.name.endswith(".bat"):
                    return cand
    w = shutil.which("kotlinc")
    return Path(w) if w else None


def extract_package(path: Path) -> Optional[str]:
    try:
        with path.open("r", encoding="utf-8", errors="ignore") as f:
            for i, line in enumerate(f):
                if i > 200:
                    break
                s = line.strip()
                if (
                    not s
                    or s.startswith(("//", "/*", "*", "#", "@"))
                ):
                    continue
                m = PACKAGE_LINE_RE.match(s)
                if m:
                    return m.group(1)
                if re.match(r"^(import|class|interface|object|enum|fun)\b", s, re.I):
                    break
    except Exception:
        return None
    return None


def infer_source_root(path: Path, package: Optional[str]) -> Path:
    if not package:
        return path.parent
    parts = package.split(".")
    root = path.parent
    if parts and len(root.parts) >= len(parts):
        if root.parts[-len(parts) :] == tuple(parts):
            for _ in parts:
                root = root.parent
            return root
    return path.parent


def aosp_default_java_classpath(root: Optional[Path]) -> List[str]:
    if not root:
        return []
    jars = []
    candidates = [
        root / "out/target/common/obj/JAVA_LIBRARIES/framework_intermediates/classes.jar",
        root / "out/target/common/obj/JAVA_LIBRARIES/framework_intermediates/classes-header.jar",
        root / "out/target/common/obj/JAVA_LIBRARIES/android_stubs_intermediates/classes.jar",
        root / "out/soong/.intermediates/frameworks/base/framework/android_common/turbine-combined/framework.jar",
    ]
    for c in candidates:
        if c.is_file():
            jars.append(str(c))
    return jars


def classify_context(sev: str, msg: str, res_list, strict: bool) -> str:
    if sev == "error" and not strict:
        for rx in res_list:
            if rx.search(msg):
                return "context"
    return sev


def parse_javac(raw: str, strict_context: bool) -> List[Diagnostic]:
    diags: List[Diagnostic] = []
    last_idx = -1
    for line in raw.splitlines():
        line = line.rstrip()
        cm = JAVAC_CARET_RE.match(line)
        if cm and last_idx >= 0:
            if diags[last_idx].col == 0:
                diags[last_idx].col = len(cm.group(1)) + 1
            continue
        if line.startswith("Note:"):
            diags.append(Diagnostic("", 0, 0, "note", "javac", line[5:].strip()))
            last_idx = -1
            continue
        m = JAVA_DIAG_RE.match(line)
        if not m:
            continue
        sev = m.group("severity").lower()
        if sev == "note":
            sev = "note"
        elif sev == "warning":
            sev = "warning"
        else:
            sev = "error"
        msg = m.group("message").strip()
        tag = ""
        if sev == "warning":
            tm = re.match(r"^\[(?P<tag>[^\]]+)\]\s+(?P<rest>.*)$", msg)
            if tm:
                tag, msg = tm.group("tag"), tm.group("rest")
                if tag == "options":
                    continue
        sev = classify_context(sev, msg, JAVA_CONTEXT_RES, strict_context)
        col = int(m.group("col")) if m.group("col") else 0
        diags.append(Diagnostic(m.group("file"), int(m.group("line")), col, sev, "javac", msg, tag))
        last_idx = len(diags) - 1
    return diags


def parse_kotlin(raw: str, strict_context: bool) -> List[Diagnostic]:
    diags: List[Diagnostic] = []
    for line in raw.splitlines():
        line = line.rstrip()
        if not line:
            continue
        m = KOTLIN_DIAG_RE.match(line) or KOTLIN_EW_DIAG_RE.match(line)
        if m:
            s_raw = m.group("severity").lower()
            sev = "error" if s_raw in {"e", "error"} else "warning"
            msg = m.group("message").strip()
            sev = classify_context(sev, msg, KOTLIN_CONTEXT_RES, strict_context)
            diags.append(Diagnostic(m.group("file"), int(m.group("line")), int(m.group("col")), sev, "kotlinc", msg))
    return diags


def run_process_capture(cmd: List[str], cwd: Optional[str], env: dict, timeout: float, label: str):
    t0 = time.time()
    try:
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=cwd, env=env)
    except FileNotFoundError:
        return "", 127, time.time() - t0, Diagnostic(label, 0, 0, "error", "aospcheck", f"Executable not found: {cmd[0]}")
    except OSError as e:
        return "", 1, time.time() - t0, Diagnostic(label, 0, 0, "error", "aospcheck", f"Subprocess start failed: {e}")

    PROC_REGISTRY.add(proc)
    try:
        out_b, err_b = proc.communicate(timeout=timeout if timeout > 0 else None)
        raw = (err_b or b"").decode("utf-8", "replace") + (out_b or b"").decode("utf-8", "replace")
        return raw, proc.returncode, time.time() - t0, None
    except subprocess.TimeoutExpired:
        try:
            proc.kill()
        except OSError:
            pass
        return "", 124, time.time() - t0, Diagnostic(label, 0, 0, "error", "aospcheck", f"Timeout after {timeout}s")
    finally:
        PROC_REGISTRY.discard(proc)


def run_java_batch(task: BatchTask, javac_bin: Path, args: argparse.Namespace, root: Optional[Path], env: dict) -> TaskResult:
    with tempfile.TemporaryDirectory(prefix="aosp_javac_") as td:
        cmd = [
            str(javac_bin),
            "-encoding", "UTF-8",
            "-proc:none",
            "-implicit:none",
            "-Xlint:all",
            "-Xmaxerrs", "10000",
            "-Xmaxwarns", "10000",
            "-d", td,
        ]
        if args.java_release:
            cmd.extend(["--release", args.java_release])
        elif args.java_source:
            cmd.extend(["-source", args.java_source])

        cp = list(args.classpath)
        if args.aosp_default_classpath and root:
            cp.extend(aosp_default_java_classpath(root))
        if cp:
            cmd.extend(["-cp", os.pathsep.join(dict.fromkeys(cp))])

        sp = list(args.sourcepath)
        for sf in task.files:
            sp.append(str(infer_source_root(sf.path, sf.package)))
        cmd.extend(["-sourcepath", os.pathsep.join(dict.fromkeys(sp))])

        if args.werror:
            cmd.append("-Werror")
        cmd.extend(args.javac_flag)
        cmd.extend(str(sf.path) for sf in task.files)

        raw, rc, dur, err_diag = run_process_capture(cmd, str(root) if root else None, env, args.timeout, task.label)
        diags = ([err_diag] if err_diag else []) + parse_javac(raw, args.strict_context)
        if rc != 0 and not any(
            d.severity in {"error", "warning", "context"} for d in diags
        ):
            diags.append(
                Diagnostic(
                    task.label,
                    0,
                    0,
                    "error",
                    "aospcheck",
                    f"javac exited with status {rc} without a diagnostic.",
                )
            )
        return TaskResult(task=task, diags=diags, raw=raw, cmd=cmd, rc=rc, duration=dur)


def run_kotlin_batch(task: BatchTask, kotlinc_bin: Path, args: argparse.Namespace, root: Optional[Path], env: dict) -> TaskResult:
    with tempfile.TemporaryDirectory(prefix="aosp_kotlinc_") as td:
        cmd = [str(kotlinc_bin), "-d", td]
        if args.kotlin_language_version:
            cmd.extend(["-language-version", args.kotlin_language_version])
        if args.kotlin_api_version:
            cmd.extend(["-api-version", args.kotlin_api_version])
        if args.kotlin_jvm_target:
            cmd.extend(["-jvm-target", args.kotlin_jvm_target])

        cp = list(args.classpath)
        if args.aosp_default_classpath and root:
            cp.extend(aosp_default_java_classpath(root))
        if cp:
            cmd.extend(["-classpath", os.pathsep.join(dict.fromkeys(cp))])

        if args.werror:
            cmd.append("-Werror")
        cmd.extend(args.kotlinc_flag)
        cmd.extend(str(sf.path) for sf in task.files)

        raw, rc, dur, err_diag = run_process_capture(cmd, str(root) if root else None, env, args.timeout, task.label)
        diags = ([err_diag] if err_diag else []) + parse_kotlin(raw, args.strict_context)
        if rc != 0 and not any(
            d.severity in {"error", "warning", "context"} for d in diags
        ):
            diags.append(
                Diagnostic(
                    task.label,
                    0,
                    0,
                    "error",
                    "aospcheck",
                    f"kotlinc exited with status {rc} without a diagnostic.",
                )
            )
        return TaskResult(task=task, diags=diags, raw=raw, cmd=cmd, rc=rc, duration=dur)


def match_diag_to_file(diag_file: str, input_files: Dict[str, str]) -> Optional[str]:
    if not diag_file:
        return None
    try:
        resolved = str(Path(diag_file).resolve())
        if resolved in input_files:
            return input_files[resolved]
    except Exception:
        pass
    norm = Path(diag_file).as_posix()
    for abs_path, orig in input_files.items():
        if abs_path.endswith(norm) or Path(abs_path).as_posix().endswith(norm):
            return orig
    return None


class Progress:
    def __init__(self, total: int, enabled: bool):
        self.total, self.enabled = total, enabled
        self.done = self.errs = self.warns = self.ctx = 0
        self.lock = threading.Lock()

    def update(self, diags: List[Diagnostic]):
        with self.lock:
            self.done += 1
            self.errs += sum(1 for d in diags if d.severity == "error")
            self.warns += sum(1 for d in diags if d.severity == "warning")
            self.ctx += sum(1 for d in diags if d.severity == "context")
            if self.enabled:
                sys.stderr.write(
                    f"\r\x1b[K  [{self.done}/{self.total}] tasks | errors: {self.errs} "
                    f"warnings: {self.warns} context: {self.ctx}"
                )
                sys.stderr.flush()

    def finish(self):
        if self.enabled:
            sys.stderr.write("\n")


def build_argparser():
    ap = argparse.ArgumentParser(
        prog="aospcheck_java_general.py",
        description="AOSP Java & Kotlin Syntax / Diagnostic Checker",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("-i", "--input", action="append", required=True, help="Input file, dir, or glob. Repeatable.")
    ap.add_argument("-j", "--jobs", type=int, default=os.cpu_count() or 4, help="Worker threads.")
    ap.add_argument("--aosp-root", help="AOSP Root directory.")
    ap.add_argument("--javac", help="Explicit path to javac binary.")
    ap.add_argument("--kotlinc", help="Explicit path to kotlinc binary.")
    ap.add_argument("-cp", "--classpath", action="append", default=[], help="Classpath elements. Repeatable.")
    ap.add_argument("-sp", "--sourcepath", action="append", default=[], help="Sourcepath elements. Repeatable.")
    ap.add_argument("--java-release", default="17", help="javac --release (Default: 17 for AOSP 14).")
    ap.add_argument("--java-source", help="javac -source.")
    ap.add_argument("--java-batch-size", type=int, default=64, help="Max Java files per javac invocation (Default: 64).")
    ap.add_argument("--kotlin-batch-size", type=int, default=32, help="Max Kotlin files per kotlinc invocation (Default: 32).")
    ap.add_argument("--kotlin-language-version", default="1.9", help="kotlinc -language-version.")
    ap.add_argument("--kotlin-api-version", default="1.9", help="kotlinc -api-version.")
    ap.add_argument("--kotlin-jvm-target", default="17", help="kotlinc -jvm-target.")
    ap.add_argument("--javac-flag", action="append", default=[], help="Extra javac flag. Repeatable.")
    ap.add_argument("--kotlinc-flag", action="append", default=[], help="Extra kotlinc flag. Repeatable.")
    ap.add_argument(
        "--aosp-default-classpath",
        dest="aosp_default_classpath",
        action="store_true",
        default=True,
        help="Include heuristic out/ target framework jars.",
    )
    ap.add_argument(
        "--no-aosp-default-classpath",
        dest="aosp_default_classpath",
        action="store_false",
        help="Do not include heuristic out/ target framework jars.",
    )
    ap.add_argument("--strict-context", action="store_true", help="Escalate missing symbol/package warnings into errors.")
    ap.add_argument("--hide-context", action="store_true", help="Hide missing dependency/symbol diagnostics.")
    ap.add_argument("-Werror", "--werror", action="store_true", help="Treat warnings as errors.")
    ap.add_argument(
        "--fail-on-warning",
        dest="werror",
        action="store_true",
        help="Treat warnings as errors (same as --werror).",
    )
    ap.add_argument("--timeout", type=float, default=240.0, help="Timeout per batch in seconds.")
    ap.add_argument("--json", help="Write JSON report to file.")
    ap.add_argument("-q", "--quiet", action="store_true", help="Suppress progress and banners.")
    ap.add_argument("--color", choices=["auto", "always", "never"], default="auto")
    return ap


def main(argv=None) -> int:
    args = build_argparser().parse_args(argv)
    color_on = sys.stdout.isatty() if args.color == "auto" else (args.color == "always")

    root = find_aosp_root(args.aosp_root, args.input)
    javac_bin, jdk_home = find_javac(root, args.javac)
    kotlinc_bin = find_kotlinc(root, args.kotlinc)

    env = dict(os.environ)
    env["LC_ALL"] = "C"
    if jdk_home:
        env["JAVA_HOME"] = str(jdk_home)

    all_files: List[Path] = []
    for item in args.input:
        if globmod.has_magic(item):
            for m in globmod.glob(item, recursive=True):
                p = Path(m).resolve()
                if p.is_file() and p.suffix.lower() in SUPPORTED_EXTS:
                    all_files.append(p)
        else:
            p = Path(item).resolve()
            if p.is_dir():
                for r, dirs, files in os.walk(p):
                    dirs[:] = [d for d in dirs if d not in SKIP_DIRS and not d.startswith(".")]
                    for f in files:
                        fp = Path(r) / f
                        if fp.suffix.lower() in SUPPORTED_EXTS:
                            all_files.append(fp)
            elif p.is_file() and p.suffix.lower() in SUPPORTED_EXTS:
                all_files.append(p)

    all_files = sorted(set(all_files))
    if not all_files:
        print("No supported Java or Kotlin files found.", file=sys.stderr)
        return EXIT_USAGE

    java_sources = []
    kotlin_sources = []
    for p in all_files:
        ext = p.suffix.lower()
        if ext in JAVA_EXTS:
            java_sources.append(SourceFile(path=p, lang="java", package=extract_package(p)))
        else:
            kotlin_sources.append(SourceFile(path=p, lang="kotlin", package=extract_package(p)))

    missing_compilers = []
    if java_sources and not javac_bin:
        missing_compilers.append("javac")
    if kotlin_sources and not kotlinc_bin:
        missing_compilers.append("kotlinc")
    if missing_compilers:
        print(
            "Required compiler(s) not found: "
            + ", ".join(missing_compilers)
            + ". Set --javac/--kotlinc or provide an AOSP tree.",
            file=sys.stderr,
        )
        return EXIT_USAGE

    tasks: List[BatchTask] = []

    def make_batches(sources: List[SourceFile], chunk_size: int, lang: str):
        groups = defaultdict(list)
        for sf in sources:
            key = sf.package if sf.package else str(sf.path.parent)
            groups[key].append(sf)
        for key, items in groups.items():
            for i in range(0, len(items), chunk_size):
                chunk = items[i : i + chunk_size]
                tasks.append(BatchTask(lang=lang, files=chunk, label=f"{key} [{len(chunk)}]"))

    make_batches(java_sources, args.java_batch_size, "java")
    make_batches(kotlin_sources, args.kotlin_batch_size, "kotlin")

    if not args.quiet:
        print(colorize(f"aospcheck_java {VERSION} — Checking {len(all_files)} files in {len(tasks)} batches", C.BOLD, color_on))
        print(f"  AOSP Root : {root or '(Not detected)'}")
        print(f"  javac     : {javac_bin or 'NOT FOUND'}")
        print(f"  kotlinc   : {kotlinc_bin or 'NOT FOUND'}")

    prog = Progress(len(tasks), sys.stderr.isatty() and not args.quiet)
    results: List[TaskResult] = []
    t0 = time.time()

    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as ex:
        futs = {}
        for t in tasks:
            if t.lang == "java":
                if not javac_bin:
                    continue
                futs[ex.submit(run_java_batch, t, javac_bin, args, root, env)] = t
            else:
                if not kotlinc_bin:
                    continue
                futs[ex.submit(run_kotlin_batch, t, kotlinc_bin, args, root, env)] = t
        try:
            for fut in as_completed(futs):
                res = fut.result()
                results.append(res)
                prog.update(res.diags)
        except KeyboardInterrupt:
            sys.stderr.write("\nInterrupted! Terminating compiler child processes...\n")
            PROC_REGISTRY.kill_all()
            return EXIT_INTERRUPT

    prog.finish()
    elapsed = time.time() - t0

    all_diags: List[Diagnostic] = []
    for r in results:
        all_diags.extend(r.diags)

    if args.werror:
        for d in all_diags:
            if d.severity == "warning":
                d.severity = "error"

    hidden_count = 0
    if args.hide_context:
        kept = []
        for d in all_diags:
            if d.severity == "context":
                hidden_count += 1
            else:
                kept.append(d)
        all_diags = kept

    cur_file = None
    for d in sorted(all_diags, key=Diagnostic.sort_key):
        if d.file != cur_file:
            cur_file = d.file
            print(colorize(f"\n-- {d.file or '<compiler>'} ({d.tool}) " + "-" * 40, C.DIM, color_on))
        sev_color = C.RED if d.severity == "error" else (C.YELLOW if d.severity == "warning" else C.MAGENTA)
        loc = f"{d.file}:{d.line}:{d.col}" if d.line else d.file
        tag_str = f" [{d.tag}]" if d.tag else ""
        print(f"{loc}: {colorize(d.severity.upper(), sev_color, color_on)}{tag_str} {d.message}")

    counts = Counter(d.severity for d in all_diags)
    print(colorize("\n" + "=" * 60, C.DIM, color_on))
    print(f"Checked {len(all_files)} files ({len(java_sources)} Java, {len(kotlin_sources)} Kotlin) in {elapsed:.2f}s")
    print(f"Errors   : {colorize(str(counts['error']), C.RED, color_on)}")
    print(f"Warnings : {colorize(str(counts['warning']), C.YELLOW, color_on)}")
    print(f"Context  : {colorize(str(counts['context']), C.MAGENTA, color_on)} (Missing dependencies)")

    if args.json:
        payload = {
            "version": VERSION,
            "elapsed_sec": round(elapsed, 2),
            "summary": dict(counts),
            "diagnostics": [asdict(d) for d in sorted(all_diags, key=Diagnostic.sort_key)],
        }
        Path(args.json).write_text(json.dumps(payload, indent=2), encoding="utf-8")
        print(f"Report saved to {args.json}")

    return EXIT_ERRORS if counts["error"] > 0 else (EXIT_WARNINGS if counts["warning"] > 0 else EXIT_OK)


if __name__ == "__main__":
    sys.exit(main())
