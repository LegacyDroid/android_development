#!/usr/bin/env python3
"""Audit LegacyDroid forks against their LineageOS upstream.

Read-only: only HTTP GET to api.github.com. Never fetches, writes, or
modifies any local git repo, index, or working tree.
"""

import json
import os
import sys
import time
import urllib.error
import urllib.request
import xml.etree.ElementTree as ET

MANIFEST_DIR = ".repo/manifests"
DEFAULT_MANIFEST = os.path.join(MANIFEST_DIR, "default.xml")
LOCAL_MANIFEST_DIR = ".repo/local_manifests"

FORK_REMOTE = "legacydroid"
UPSTREAM_OWNER = "LineageOS"
FORK_OWNER = "LegacyDroid"

# Fork branches that track a differently named upstream branch.
BRANCH_OVERRIDES = {"legacydroid-14": "lineage-21.0"}

API = "https://api.github.com"


def strip_ns(tag):
    return tag.rsplit("}", 1)[-1] if "}" in tag else tag


def load_manifests():
    paths = []
    if os.path.isdir(LOCAL_MANIFEST_DIR):
        for name in sorted(os.listdir(LOCAL_MANIFEST_DIR)):
            if name.endswith(".xml"):
                paths.append(os.path.join(LOCAL_MANIFEST_DIR, name))
    paths.append(DEFAULT_MANIFEST)
    return [p for p in paths if os.path.isfile(p)]


def parse_forks(manifests):
    forks = []
    for path in manifests:
        try:
            root = ET.parse(path).getroot()
        except ET.ParseError as err:
            print(f"warn: cannot parse {path}: {err}", file=sys.stderr)
            continue
        for elem in root.iter():
            if strip_ns(elem.tag) != "project":
                continue
            attrib = {strip_ns(k): v for k, v in elem.attrib.items()}
            if attrib.get("remote") != FORK_REMOTE:
                continue
            name = attrib.get("name", "")
            repo = name.split("/")[-1]
            branch = attrib.get("revision", "refs/heads/legacydroid-14")
            branch = branch.replace("refs/heads/", "")
            forks.append({
                "manifest": path,
                "path": attrib.get("path", "?"),
                "name": name,
                "repo": repo,
                "branch": branch,
            })
    seen, unique = set(), []
    for f in forks:
        if f["name"] in seen:
            continue
        seen.add(f["name"])
        unique.append(f)
    return unique


def api_get(path, token):
    url = f"{API}{path}"
    req = urllib.request.Request(url, headers={
        "Accept": "application/vnd.github+json",
        "User-Agent": "legacydroid-fork-audit",
    })
    if token:
        req.add_header("Authorization", f"Bearer {token}")
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            return json.load(resp)
    except urllib.error.HTTPError as err:
        return {"__status__": err.code, "__body__": err.read().decode(errors="replace")}
    except urllib.error.URLError as err:
        return {"__status__": 0, "__body__": str(err)}


def check(fork, token):
    repo = fork["repo"]
    meta = api_get(f"/repos/{FORK_OWNER}/{repo}", token)
    code = meta.get("__status__", 200)
    if code == 404:
        return {**fork, "skipped": "repo not found on GitHub"}
    if code != 200:
        return {**fork, "skipped": f"api error {code}"}

    # Trust GitHub fork metadata over any name guessing.
    parent = (meta.get("parent") or {}).get("full_name") or \
             (meta.get("source") or {}).get("full_name")
    if not parent:
        return {**fork, "origin": "own code (no fork parent)",
                "skipped": "not a fork of anything"}
    if not parent.startswith(UPSTREAM_OWNER + "/"):
        return {**fork, "origin": parent,
                "skipped": f"forked from {parent}, not {UPSTREAM_OWNER}"}

    upstream_branch = BRANCH_OVERRIDES.get(fork["branch"]) or meta.get("default_branch")
    head = f"{FORK_OWNER}:{fork['branch']}"
    cmp_path = f"/repos/{parent}/compare/{upstream_branch}...{head}"
    data = api_get(cmp_path, token)
    code = data.get("__status__", 200)
    if code != 200:
        return {**fork, "origin": parent, "upstream_branch": upstream_branch,
                "skipped": f"compare failed {code}: {data.get('__body__', '')[:70]}"}

    return {
        **fork,
        "origin": parent,
        "upstream": parent,
        "upstream_branch": upstream_branch,
        "behind": data.get("behind_by"),
        "ahead": data.get("ahead_by"),
        "status": data.get("status"),
        "skipped": None,
    }


def main():
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if not os.path.isdir(MANIFEST_DIR):
        print(f"error: {MANIFEST_DIR} not found; run from tree root", file=sys.stderr)
        return 2

    manifests = load_manifests()
    forks = parse_forks(manifests)
    if not forks:
        print(f"No projects with remote=\"{FORK_REMOTE}\" found.")
        return 0

    print(f"Forks declared under remote=\"{FORK_REMOTE}\": {len(forks)}")
    print(f"Manifests: {', '.join(manifests)}")
    if not token:
        print("No GITHUB_TOKEN set; unauthenticated limit is 60 req/hour.\n")

    results = []
    for fork in forks:
        results.append(check(fork, token))
        time.sleep(0.2)

    tracked = [r for r in results if r["skipped"] is None]
    skipped = [r for r in results if r["skipped"] is not None]
    tracked.sort(key=lambda r: (-(r["behind"] or 0), r["repo"]))

    if tracked:
        print(f"\nLineageOS forks ({len(tracked)}) -- commits BEHIND upstream")
        print(f"{'BEHIND':>7}  {'AHEAD':>6}  {'UPSTREAM BRANCH':<18} {'REPO':<42} PATH")
        for r in tracked:
            flag = "  <-- needs merge" if (r["behind"] or 0) > 0 else ""
            print(f"{r['behind']:>7}  {r['ahead']:>6}  {r['upstream_branch']:<18} "
                  f"{r['repo']:<42} {r['path']}{flag}")

    if skipped:
        print(f"\nSkipped, not {UPSTREAM_OWNER} forks ({len(skipped)})")
        for r in skipped:
            print(f"  {r['repo']:<42} {r['path']:<32} {r['skipped']}")

    behind_total = sum(r["behind"] or 0 for r in tracked)
    print(f"\nForks behind upstream: {sum(1 for r in tracked if (r['behind'] or 0) > 0)}"
          f"/{len(tracked)}   commits to merge: {behind_total}")
    if behind_total:
        print("Merge with: repo start <path>  (or repo sync, which merges upstream)")
    return 0


if __name__ == "__main__":
    sys.exit(main())