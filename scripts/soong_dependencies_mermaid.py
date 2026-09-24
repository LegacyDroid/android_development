#!/usr/bin/env python3
"""Create a bounded Mermaid dependency graph from a real AOSP Ninja file.

The tool reads the generated Ninja graph through Ninja itself, then uses
module-info metadata to collapse raw action/file nodes into logical modules.
It never runs lunch, m, soong_ui, or Ninja in build mode by itself.
"""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import html
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from collections import defaultdict, deque
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple


EXIT_OK = 0
EXIT_USAGE = 2
EXIT_DATA = 3
EXIT_LIMIT = 4

VARIANTS = {"eng", "user", "userdebug", "debug"}
DEPENDENCY_FIELDS = (
    "dependencies",
    "shared_libs",
    "static_libs",
    "system_shared_libs",
    "java_libs",
    "libs",
    "frameworks",
)


class GraphError(Exception):
    """A user-facing graph generation error."""


class GraphLimit(GraphError):
    """The requested graph exceeded a configured safety limit."""


@dataclass(frozen=True)
class LunchTarget:
    raw: str
    product: str
    release: str
    variant: str


@dataclass
class ModuleRecord:
    key: str
    name: str
    path: Tuple[str, ...] = ()
    installed: Tuple[str, ...] = ()
    classes: Tuple[str, ...] = ()
    variants: Tuple[str, ...] = ()
    dependencies: Tuple[str, ...] = ()

    @property
    def display_path(self) -> str:
        return self.path[0] if self.path else ""


@dataclass
class Catalog:
    records: List[ModuleRecord]
    primary: Dict[str, ModuleRecord]
    output_to_module: Dict[str, str] = field(default_factory=dict)
    path_to_module: Dict[str, str] = field(default_factory=dict)
    alias_to_module: Dict[str, str] = field(default_factory=dict)
    basename_to_module: Dict[str, str] = field(default_factory=dict)

    def resolve(self, label: str) -> Optional[str]:
        """Map a Ninja node label to a logical module name when unambiguous."""
        value = unescape_dot(label).strip()
        if not value:
            return None

        value = value.replace("\\", "/")
        if value.startswith("./"):
            value = value[2:]
        out_index = value.find("/out/")
        if out_index >= 0:
            value = value[out_index + 1 :]
        elif value.startswith("/out/"):
            value = value[1:]

        for candidate in (value, value.rstrip("/"), value.replace(".so", "")):
            if candidate in self.output_to_module:
                return self.output_to_module[candidate]
            if candidate in self.alias_to_module:
                return self.alias_to_module[candidate]
            for suffix in ("-soong", "-checkbuild", "-install"):
                if candidate.endswith(suffix):
                    base_name = candidate[: -len(suffix)]
                    if base_name in self.primary:
                        return base_name

        base = value.rsplit("/", 1)[-1]
        if base in self.basename_to_module:
            return self.basename_to_module[base]

        parts = value.split("/")
        for end in range(len(parts), 0, -1):
            prefix = "/".join(parts[:end])
            if prefix in self.path_to_module:
                return self.path_to_module[prefix]
        return None

    def label(self, name: str) -> str:
        record = self.primary.get(name)
        if not record:
            return name
        return name


@dataclass
class RawNode:
    label: str
    action: bool = False


@dataclass
class Graph:
    nodes: Dict[str, str] = field(default_factory=dict)
    classes: Dict[str, str] = field(default_factory=dict)
    edges: Set[Tuple[str, str]] = field(default_factory=set)
    source: str = ""

    def add_node(self, name: str, label: Optional[str] = None, class_name: str = "module") -> None:
        if name not in self.nodes:
            self.nodes[name] = label or name
        self.classes[name] = class_name

    def add_edge(self, source: str, target: str) -> None:
        if source != target:
            self.edges.add((source, target))
            self.add_node(source)
            self.add_node(target)


def parse_lunch(value: str) -> LunchTarget:
    parts = value.rsplit("-", 2)
    if len(parts) != 3 or not all(parts):
        raise GraphError(
            f"invalid lunch target {value!r}; expected PRODUCT-RELEASE-VARIANT"
        )
    product, release, variant = parts
    if variant not in VARIANTS:
        raise GraphError(
            f"invalid lunch variant {variant!r}; expected one of {', '.join(sorted(VARIANTS))}"
        )
    return LunchTarget(value, product, release, variant)


def find_top(explicit: Optional[str]) -> Path:
    candidates: List[Path] = []
    if explicit:
        candidates.append(Path(explicit).expanduser().resolve())
    cwd = Path.cwd().resolve()
    candidates.extend([cwd, *cwd.parents])
    script = Path(__file__).resolve()
    candidates.extend(script.parents)
    for candidate in candidates:
        if (candidate / "build" / "soong" / "soong_ui.bash").is_file():
            return candidate
    raise GraphError("could not locate the AOSP source tree; pass --top")


def load_json(path: Path):
    try:
        with path.open("r", encoding="utf-8") as stream:
            return json.load(stream)
    except (OSError, json.JSONDecodeError) as exc:
        raise GraphError(f"could not read JSON {path}: {exc}") from exc


def discover_paths(top: Path, target: LunchTarget, out_dir: Path, source: str) -> Tuple[Path, Path]:
    product = target.product
    if source == "combined":
        ninja_file = out_dir / f"combined-{product}.ninja"
    else:
        ninja_file = out_dir / "soong" / f"build.{product}.ninja"
    if not ninja_file.is_file():
        raise GraphError(
            f"missing {source} Ninja file: {ninja_file}\n"
            "Generate it first with the existing no-module-build flow, for example:\n"
            "  source build/envsetup.sh\n"
            "  lunch "
            f"{target.raw}\n"
            "  m --soong-only --skip-ninja nothing"
        )

    variables_path = out_dir / "soong" / f"soong.{product}.variables"
    product_dir: Optional[Path] = None
    if variables_path.is_file():
        variables = load_json(variables_path)
        device_name = variables.get("DeviceName")
        if isinstance(device_name, str) and device_name:
            candidate = out_dir / "target" / "product" / device_name
            if candidate.is_dir():
                product_dir = candidate

    if product_dir is None:
        candidates = sorted((out_dir / "target" / "product").glob("*/module-info.json"))
        if len(candidates) == 1:
            product_dir = candidates[0].parent

    module_info = product_dir / "module-info.json" if product_dir else None
    if module_info is None or not module_info.is_file():
        fallback = out_dir / "soong" / f"module-info-{product}.json"
        if fallback.is_file():
            module_info = fallback
    if module_info is None or not module_info.is_file():
        raise GraphError(
            f"could not find module-info.json for {product}; expected under "
            f"{out_dir / 'target' / 'product'} or {out_dir / 'soong'}"
        )
    return ninja_file, module_info


def find_ninja(top: Path) -> Path:
    candidates = [
        top / "prebuilts" / "build-tools" / "linux-x86" / "bin" / "ninja",
        top / "prebuilts" / "build-tools" / "darwin-x86" / "bin" / "ninja",
    ]
    for candidate in candidates:
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return candidate
    system = shutil.which("ninja")
    if system:
        return Path(system)
    raise GraphError("could not find Ninja; expected under prebuilts/build-tools")


def prepare_ninja_manifest(ninja_file: Path, source: str, out_dir: Path) -> Tuple[Path, Optional[Path]]:
    if source != "soong":
        return ninja_file, None
    stream = tempfile.NamedTemporaryFile(
        mode="w",
        prefix=".soong-mermaid-",
        suffix=".ninja",
        dir=str(out_dir),
        delete=False,
        encoding="utf-8",
    )
    try:
        stream.write("pool highmem_pool\n  depth = 1\n")
        stream.write(f"include {ninja_file}\n")
        stream.close()
    except Exception:
        stream.close()
        Path(stream.name).unlink(missing_ok=True)
        raise
    return Path(stream.name), Path(stream.name)


def as_records(raw) -> Iterable[Tuple[str, dict]]:
    if isinstance(raw, dict):
        for key, value in raw.items():
            if isinstance(value, dict):
                yield str(key), value
        return
    if isinstance(raw, list):
        for element in raw:
            if isinstance(element, dict):
                for key, value in element.items():
                    if isinstance(value, dict):
                        yield str(key), value


def record_dependencies(value: dict) -> Tuple[str, ...]:
    result: List[str] = []
    for field in DEPENDENCY_FIELDS:
        entries = value.get(field)
        if not isinstance(entries, list):
            continue
        for entry in entries:
            if isinstance(entry, str) and entry and entry != "none":
                result.append(entry)
    return tuple(dict.fromkeys(result))


def record_score(record: ModuleRecord) -> Tuple[int, int, int]:
    variants = set(record.variants)
    classes = set(record.classes)
    return (
        1 if "DEVICE" in variants else 0,
        1 if "HOST_CROSS" not in variants else 0,
        1 if any("TEST" in item for item in classes) else 0,
    )


def load_catalog(path: Path) -> Catalog:
    raw = load_json(path)
    records: List[ModuleRecord] = []
    for key, value in as_records(raw):
        name = value.get("module_name")
        if not isinstance(name, str) or not name:
            continue
        path_value = value.get("path")
        installed = value.get("installed")
        classes = value.get("class")
        variants = value.get("supported_variants")
        records.append(
            ModuleRecord(
                key=key,
                name=name,
                path=tuple(str(item) for item in path_value if isinstance(item, str))
                if isinstance(path_value, list)
                else (),
                installed=tuple(str(item) for item in installed if isinstance(item, str))
                if isinstance(installed, list)
                else (),
                classes=tuple(str(item) for item in classes if isinstance(item, str))
                if isinstance(classes, list)
                else (),
                variants=tuple(str(item) for item in variants if isinstance(item, str))
                if isinstance(variants, list)
                else (),
                dependencies=record_dependencies(value),
            )
        )
    if not records:
        raise GraphError(f"module-info contains no module records: {path}")

    grouped: Dict[str, List[ModuleRecord]] = defaultdict(list)
    for record in records:
        grouped[record.name].append(record)
    primary = {
        name: max(items, key=record_score)
        for name, items in grouped.items()
    }

    catalog = Catalog(records=records, primary=primary)
    path_groups: Dict[str, List[ModuleRecord]] = defaultdict(list)
    output_groups: Dict[str, List[ModuleRecord]] = defaultdict(list)
    basename_groups: Dict[str, List[ModuleRecord]] = defaultdict(list)
    ordered_records = sorted(records, key=record_score, reverse=True)
    for record in ordered_records:
        module = record.name
        catalog.alias_to_module.setdefault(module, module)
        catalog.alias_to_module.setdefault(record.key, module)
        for output in record.installed:
            normalized = normalize_path(output)
            output_groups[normalized].append(record)
            basename_groups[normalized.rsplit("/", 1)[-1]].append(record)
        for directory in record.path:
            normalized = normalize_path(directory).rstrip("/")
            if normalized:
                path_groups[normalized].append(record)

    for output, items in output_groups.items():
        catalog.output_to_module[output] = max(items, key=record_score).name
    for directory, items in path_groups.items():
        directory_name = directory.rsplit("/", 1)[-1]
        catalog.path_to_module[directory] = min(
            items,
            key=lambda record: (
                0 if record.name == directory_name else 1,
                len(record.name),
                tuple(-value for value in record_score(record)),
                record.key,
            ),
        ).name
    for basename, items in basename_groups.items():
        stem = basename.rsplit(".", 1)[0]
        catalog.basename_to_module[basename] = min(
            items,
            key=lambda record: (
                0 if record.name == stem else 1,
                len(record.name),
                tuple(-value for value in record_score(record)),
                record.key,
            ),
        ).name
    return catalog


def normalize_path(value: str) -> str:
    value = value.replace("\\", "/")
    while value.startswith("./"):
        value = value[2:]
    return value


def record_class(record: Optional[ModuleRecord]) -> str:
    if not record:
        return "other"
    classes = " ".join(record.classes).upper()
    if "TEST" in classes:
        return "test"
    if "EXECUTABLE" in classes:
        return "executable"
    if "APP" in classes:
        return "app"
    if "JAVA" in classes:
        return "java"
    if "LIBRARY" in classes:
        return "library"
    return "module"


def unescape_dot(value: str) -> str:
    value = value.replace(r"\"", '"').replace(r"\\", "\\")
    value = value.replace(r"\n", " ").replace(r"\t", " ").replace(r"\r", " ")
    return value


def parse_dot_label(attrs: str) -> str:
    match = re.search(r'label="((?:\\.|[^"\\])*)"', attrs)
    if match:
        return unescape_dot(match.group(1))
    match = re.search(r"label=([^,\]]+)", attrs)
    return unescape_dot(match.group(1).strip()) if match else ""


NODE_RE = re.compile(r'^\s*("(?:\\.|[^"\\])*"|[^\s\[]+)\s*\[(.*)\]\s*;?\s*$')
EDGE_RE = re.compile(
    r'^\s*("(?:\\.|[^"\\])*"|[^\s\[]+)\s*->\s*'
    r'("(?:\\.|[^"\\])*"|[^\s\[]+)(?:\s*\[.*\])?\s*;?\s*$'
)


def dot_id(value: str) -> str:
    if len(value) >= 2 and value[0] == '"' and value[-1] == '"':
        return unescape_dot(value[1:-1])
    return value


def run_ninja_graph(
    ninja: Path,
    ninja_file: Path,
    targets: Sequence[str],
    max_nodes: int,
    max_edges: int,
    cwd: Path,
) -> Tuple[Dict[str, RawNode], List[Tuple[str, str]]]:
    command = [str(ninja), "-f", str(ninja_file), "-t", "graph", *targets]
    process = subprocess.Popen(
        command,
        cwd=str(cwd),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    nodes: Dict[str, RawNode] = {}
    edges: List[Tuple[str, str]] = []
    limited = False
    assert process.stdout is not None
    try:
        for line in process.stdout:
            node_match = NODE_RE.match(line)
            if node_match and dot_id(node_match.group(1)) not in {"node", "edge", "graph"}:
                node_id = dot_id(node_match.group(1))
                attrs = node_match.group(2)
                nodes[node_id] = RawNode(
                    parse_dot_label(attrs),
                    action="shape=ellipse" in attrs,
                )
                if len(nodes) > max_nodes:
                    limited = True
                    break
                continue
            edge_match = EDGE_RE.match(line)
            if edge_match:
                edges.append((dot_id(edge_match.group(1)), dot_id(edge_match.group(2))))
                if len(edges) > max_edges:
                    limited = True
                    break
    finally:
        if limited and process.poll() is None:
            process.terminate()
        stderr = process.stderr.read() if process.stderr is not None else ""
        return_code = process.wait()

    if limited:
        raise GraphLimit(
            f"Ninja graph exceeded limits ({max_nodes} nodes/{max_edges} edges); "
            "select a narrower root or raise the limits"
        )
    if return_code != 0:
        detail = stderr.strip() or f"Ninja exited with status {return_code}"
        raise GraphError(detail)
    return nodes, edges


def find_soong_target(
    ninja: Path,
    ninja_file: Path,
    module: str,
    catalog: Catalog,
    cwd: Path,
) -> str:
    record = catalog.primary[module]
    module_path = record.display_path
    if not module_path:
        raise GraphError(f"module {module!r} has no source path for Soong target discovery")
    command = [str(ninja), "-f", str(ninja_file), "-t", "targets", "all"]
    process = subprocess.Popen(
        command,
        cwd=str(cwd),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    assert process.stdout is not None
    found: Optional[str] = None
    fallback: Optional[str] = None
    scanned = 0
    preferred_extensions = (".so", ".apk", ".jar", ".zip", ".aar", ".dex", ".rc")
    for line in process.stdout:
        scanned += 1
        if scanned > 5_000_000:
            break
        target = line.split(":", 1)[0].strip()
        basename = target.rsplit("/", 1)[-1]
        if f"/{module_path}/" not in f"/{target}":
            continue
        if basename == module:
            found = target
            break
        if (
            fallback is None
            and basename.startswith(module + "_")
            and not basename.endswith((".o", ".a"))
        ):
            fallback = target
        if basename.startswith(module) and basename.endswith(preferred_extensions):
            fallback = target
    if process.poll() is None:
        process.terminate()
    stderr = process.stderr.read() if process.stderr is not None else ""
    process.wait()
    if found:
        return found
    if fallback:
        return fallback
    detail = stderr.strip()
    if detail:
        raise GraphError(detail)
    raise GraphError(f"could not find a Soong Ninja target for module {module!r}")


def roots_for_modules(
    modules: Sequence[str],
    catalog: Catalog,
    source: str,
    ninja: Optional[Path] = None,
    ninja_file: Optional[Path] = None,
    cwd: Optional[Path] = None,
) -> List[str]:
    missing = [module for module in modules if module not in catalog.primary]
    if missing:
        raise GraphError("module-info does not contain: " + ", ".join(missing))
    targets: List[str] = []
    for module in modules:
        if source == "soong" and ninja is not None and ninja_file is not None and cwd is not None:
            targets.append(find_soong_target(ninja, ninja_file, module, catalog, cwd))
        elif source == "soong":
            record = catalog.primary[module]
            installed = [
                output
                for output in record.installed
                if "/target/product/" in output
                and not output.endswith("/")
            ]
            targets.append(installed[0] if installed else module)
        else:
            targets.append(f"{module}-soong")
    return targets


def exact_graph(
    modules: Sequence[str],
    explicit_targets: Sequence[str],
    catalog: Catalog,
    ninja: Path,
    ninja_file: Path,
    max_raw_nodes: int,
    max_raw_edges: int,
    cwd: Path,
    source: str,
) -> Tuple[Graph, List[str]]:
    source_kind = source
    if not modules and not explicit_targets:
        raise GraphError("exact Ninja mode requires --module or --ninja-target")
    targets = list(explicit_targets)
    root_modules = list(modules)
    if not targets:
        targets = roots_for_modules(
            modules, catalog, source, ninja, ninja_file, cwd
        )
    raw_nodes, raw_edges = run_ninja_graph(
        ninja, ninja_file, targets, max_raw_nodes, max_raw_edges, cwd
    )
    incoming: Dict[str, Set[str]] = defaultdict(set)
    for source, target in raw_edges:
        incoming[target].add(source)

    root_ids: List[str] = []
    for target in targets:
        matching = [node_id for node_id, node in raw_nodes.items() if node.label == target]
        if not matching:
            raise GraphError(f"Ninja graph did not contain requested target {target!r}")
        root_ids.extend(matching)

    edges: Set[Tuple[str, str]] = set()
    for root_id in root_ids:
        root_module = catalog.resolve(raw_nodes[root_id].label)
        if not root_module and root_id in catalog.alias_to_module:
            root_module = catalog.alias_to_module[root_id]
        if not root_module:
            continue
        seen: Set[str] = set()
        stack = list(incoming.get(root_id, ()))
        while stack:
            node_id = stack.pop()
            if node_id in seen:
                continue
            seen.add(node_id)
            node = raw_nodes.get(node_id)
            dependency = catalog.resolve(node.label) if node else None
            if dependency:
                if dependency != root_module:
                    edges.add((root_module, dependency))
                    continue
            stack.extend(incoming.get(node_id, ()))

    graph = Graph(source=f"ninja:{source_kind}")
    for root in root_modules or [catalog.resolve(raw_nodes[i].label) or raw_nodes[i].label for i in root_ids]:
        if root:
            graph.add_node(root, catalog.label(root), record_class(catalog.primary.get(root)))
    for source, target in edges:
        graph.add_edge(source, target)
        graph.add_node(source, catalog.label(source), record_class(catalog.primary.get(source)))
        graph.add_node(target, catalog.label(target), record_class(catalog.primary.get(target)))
    return graph, root_modules


def semantic_graph(
    modules: Sequence[str], catalog: Catalog, all_modules: bool
) -> Tuple[Graph, List[str]]:
    if all_modules:
        roots = sorted(catalog.primary)
    else:
        roots = list(modules)
    if not roots:
        raise GraphError("semantic mode requires --module or --all-modules")
    missing = [module for module in roots if module not in catalog.primary]
    if missing:
        raise GraphError("module-info does not contain: " + ", ".join(missing))

    graph = Graph(source="module-info")
    for name in catalog.primary:
        record = catalog.primary[name]
        deps = [dep for dep in record.dependencies if dep in catalog.primary or dep]
        for dep in deps:
            graph.add_edge(name, dep)
        graph.add_node(name, name, record_class(record))
    return graph, roots


def restrict_graph(
    graph: Graph,
    roots: Sequence[str],
    direction: str,
    depth: int,
    max_nodes: int,
    max_edges: int,
) -> Graph:
    adjacency: Dict[str, Set[str]] = defaultdict(set)
    for source, target in graph.edges:
        if direction == "rdeps":
            adjacency[target].add(source)
        elif direction == "both":
            adjacency[source].add(target)
            adjacency[target].add(source)
        else:
            adjacency[source].add(target)

    selected: Set[str] = set()
    frontier = deque((root, 0) for root in roots)
    for root in roots:
        selected.add(root)
    while frontier:
        node, level = frontier.popleft()
        if depth >= 0 and level >= depth:
            continue
        for neighbor in sorted(adjacency.get(node, ())):
            if neighbor not in selected:
                selected.add(neighbor)
                frontier.append((neighbor, level + 1))
                if len(selected) > max_nodes:
                    raise GraphLimit(
                        f"graph exceeded --max-nodes={max_nodes}; select fewer roots "
                        "or reduce --depth"
                    )

    result = Graph(source=graph.source)
    for node in sorted(selected):
        result.add_node(
            node,
            graph.nodes.get(node, node),
            graph.classes.get(node, "module"),
        )
    selected_edges = {
        (source, target)
        for source, target in graph.edges
        if source in selected and target in selected
    }
    if len(selected_edges) > max_edges:
        raise GraphLimit(
            f"graph exceeded --max-edges={max_edges}; select fewer roots or reduce --depth"
        )
    result.edges = selected_edges
    return result


def mermaid_id(name: str, used: Dict[str, str]) -> str:
    digest = hashlib.sha256(name.encode("utf-8", "surrogatepass")).hexdigest()[:12]
    candidate = f"m_{digest}"
    if candidate not in used:
        used[candidate] = name
        return candidate
    if used[candidate] == name:
        return candidate
    suffix = 2
    while f"{candidate}_{suffix}" in used:
        suffix += 1
    candidate = f"{candidate}_{suffix}"
    used[candidate] = name
    return candidate


def mermaid_label(value: str) -> str:
    value = "".join(" " if ord(char) < 32 else char for char in value)
    value = html.escape(value, quote=True).replace("`", "&#96;")
    return value.replace("[", "&#91;").replace("]", "&#93;")


def render_mermaid(graph: Graph, target: LunchTarget) -> str:
    used: Dict[str, str] = {}
    ids = {name: mermaid_id(name, used) for name in sorted(graph.nodes)}
    lines = [
        "%%{init: {\"flowchart\": {\"htmlLabels\": false}}}%%",
        "flowchart LR",
        f"  %% lunch={target.raw}",
        f"  %% source={graph.source}",
        f"  %% nodes={len(graph.nodes)} edges={len(graph.edges)}",
    ]
    for name in sorted(graph.nodes):
        label = mermaid_label(graph.nodes[name])
        lines.append(f'  {ids[name]}["{label}"]')
    for source, target_name in sorted(graph.edges):
        lines.append(f"  {ids[source]} --> {ids[target_name]}")
    classes = defaultdict(list)
    for name in sorted(graph.nodes):
        classes[graph.classes.get(name, "module")].append(ids[name])
    class_colors = {
        "root": "fill:#dbeafe,stroke:#2563eb",
        "module": "fill:#f8fafc,stroke:#64748b",
        "library": "fill:#ecfdf5,stroke:#059669",
        "executable": "fill:#fef3c7,stroke:#d97706",
        "app": "fill:#fce7f3,stroke:#db2777",
        "java": "fill:#ede9fe,stroke:#7c3aed",
        "test": "fill:#f1f5f9,stroke:#64748b",
        "other": "fill:#ffffff,stroke:#94a3b8",
    }
    for class_name in sorted(classes):
        safe_class = re.sub(r"[^A-Za-z0-9_]", "_", class_name) or "other"
        color = class_colors.get(class_name, class_colors["other"])
        lines.append(f"  classDef {safe_class} {color};")
        lines.append(f"  class {','.join(classes[class_name])} {safe_class};")
    return "\n".join(lines) + "\n"


def list_modules(modules: Sequence[str], all_modules: bool, catalog: Catalog) -> int:
    if all_modules:
        names = sorted(catalog.primary)
    else:
        names = []
        for pattern in modules:
            matches = [
                name
                for name in sorted(catalog.primary)
                if name == pattern or fnmatch.fnmatch(name, pattern)
            ]
            if not matches:
                raise GraphError(f"no module matched {pattern!r}")
            names.extend(matches)
    for name in dict.fromkeys(names):
        record = catalog.primary[name]
        print(f"{name}\t{record.display_path}\t{','.join(record.classes)}")
    return EXIT_OK


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Render a bounded Mermaid graph from a generated AOSP Ninja file."
    )
    parser.add_argument("--lunch", help="lunch target: PRODUCT-RELEASE-VARIANT")
    parser.add_argument("--top", help="AOSP source tree root")
    parser.add_argument("--out-dir", help="output directory (default: TOP/out)")
    parser.add_argument("--source", choices=("combined", "soong"), default="combined")
    parser.add_argument("--mode", choices=("exact", "semantic"), default="exact")
    parser.add_argument("--module", action="append", default=[], help="module root; repeatable")
    parser.add_argument(
        "--ninja-target", action="append", default=[], help="exact Ninja target; repeatable"
    )
    parser.add_argument("--all-modules", action="store_true", help="use all module-info records as roots")
    parser.add_argument("--list", action="store_true", help="list matching modules and exit")
    parser.add_argument("--direction", choices=("deps", "rdeps", "both"), default="deps")
    parser.add_argument("--depth", type=int, default=1, help="dependency depth; -1 means unlimited")
    parser.add_argument("--max-nodes", type=int, default=250)
    parser.add_argument("--max-edges", type=int, default=1000)
    parser.add_argument("--max-raw-nodes", type=int, default=200000)
    parser.add_argument("--max-raw-edges", type=int, default=500000)
    parser.add_argument("--output", default="-", help="Mermaid output file, or - for stdout")
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        if args.lunch:
            target = parse_lunch(args.lunch)
        else:
            product = os.environ.get("TARGET_PRODUCT")
            release = os.environ.get("TARGET_RELEASE")
            variant = os.environ.get("TARGET_BUILD_VARIANT")
            if not (product and release and variant):
                raise GraphError("provide --lunch or set TARGET_PRODUCT, TARGET_RELEASE, and TARGET_BUILD_VARIANT")
            target = parse_lunch(f"{product}-{release}-{variant}")

        top = find_top(args.top)
        out_dir = Path(args.out_dir).expanduser().resolve() if args.out_dir else top / "out"
        ninja_file, module_info = discover_paths(top, target, out_dir, args.source)
        catalog = load_catalog(module_info)

        if args.list:
            return list_modules(args.module, args.all_modules, catalog)

        if args.all_modules and args.mode == "exact":
            raise GraphError("--all-modules is only supported with --mode semantic")

        if args.mode == "exact":
            ninja_manifest, cleanup_manifest = prepare_ninja_manifest(
                ninja_file, args.source, out_dir
            )
            try:
                graph, roots = exact_graph(
                    args.module,
                    args.ninja_target,
                    catalog,
                    find_ninja(top),
                    ninja_manifest,
                    args.max_raw_nodes,
                    args.max_raw_edges,
                    top,
                    args.source,
                )
            finally:
                if cleanup_manifest is not None:
                    cleanup_manifest.unlink(missing_ok=True)
        else:
            graph, roots = semantic_graph(args.module, catalog, args.all_modules)
            if args.ninja_target:
                raise GraphError("--ninja-target requires --mode exact")

        graph = restrict_graph(
            graph, roots, args.direction, args.depth, args.max_nodes, args.max_edges
        )
        output = render_mermaid(graph, target)
        if args.output == "-":
            sys.stdout.write(output)
        else:
            output_path = Path(args.output).expanduser()
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(output, encoding="utf-8")
            print(f"wrote {output_path} ({len(graph.nodes)} nodes, {len(graph.edges)} edges)")
        return EXIT_OK
    except GraphLimit as exc:
        print(f"error: {exc}", file=sys.stderr)
        return EXIT_LIMIT
    except GraphError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return EXIT_DATA
    except KeyboardInterrupt:
        print("interrupted", file=sys.stderr)
        return 130


if __name__ == "__main__":
    sys.exit(main())
