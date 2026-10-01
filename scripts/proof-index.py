#!/usr/bin/env python3
# Copyright (c) 2026 Jinzhao Wang. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Jinzhao Wang (AI-assisted formalization)

"""Search committed Lean metadata, or regenerate it from elaborated proof terms.

Querying requires only Python 3.9+. Regeneration builds the completed solution
with the repository's pinned Lean/dependencies. No challenge is imported.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
INDEX = ROOT / "docs" / "proof-index.json"
DESCRIPTIONS = ROOT / "docs" / "lemma-descriptions.json"
TARGETS = [
    "QuantumChannelContinuity.theorem_one",
    "QuantumChannelContinuity.blockRenyi_tendsto_regularized",
    "QuantumChannelContinuity.blockRelative_tendsto_regularized",
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path, data):
    # This is generated data. Queries provide a readable view without storing
    # several megabytes of indentation alongside the exact expression edges.
    path.write_text(json.dumps(data, ensure_ascii=False, separators=(",", ":")) + "\n",
                    encoding="utf-8")


def closure(nodes, initial):
    seen = set()
    pending = list(initial)
    while pending:
        name = pending.pop()
        if name in seen or name not in nodes:
            continue
        seen.add(name)
        node = nodes[name]
        pending.extend(node["typeDeps"])
        pending.extend(node["proofDeps"])
    return seen


def regenerate():
    source_files = sorted(set(
        list((ROOT / "ChannelContinuity").rglob("*.lean")) +
        list((ROOT / "QuantumChannelContinuity").rglob("*.lean")) +
        [ROOT / "ChannelRenyiContinuity.lean", ROOT / "lean-toolchain",
         ROOT / "lakefile.toml", ROOT / "lake-manifest.json"]
    ))
    hashes_before = {str(p.relative_to(ROOT)): digest(p) for p in source_files}
    subprocess.run([str(ROOT / "run-lake.sh"), "build", "ChannelRenyiContinuity"],
                   cwd=ROOT, check=True)
    output = ROOT / ".lake" / "proof-index"
    output.mkdir(parents=True, exist_ok=True)
    subprocess.run([str(ROOT / "run-lake.sh"), "env", "lean",
                    "scripts/ExportProofIndex.lean"], cwd=ROOT, check=True)
    raw = read_json(output / "raw.json")
    nodes = {d["name"]: d for d in raw["declarations"]}
    if any(target not in nodes for target in TARGETS):
        raise ValueError("The completed solution is missing a required target")
    curated = read_json(DESCRIPTIONS)
    by_name = curated["declarations"]
    if set(by_name) - set(nodes):
        raise ValueError("Curated descriptions name missing declarations: " +
                         ", ".join(sorted(set(by_name) - set(nodes))))
    per_target = {t: closure(nodes, [t]) for t in TARGETS}
    reverse = {n: {"typeUsers": [], "proofUsers": []} for n in nodes}
    for node in raw["declarations"]:
        for field, user_field in (("typeDeps", "typeUsers"), ("proofDeps", "proofUsers")):
            if len(node[field]) != len(set(node[field])):
                raise ValueError("Extractor emitted duplicate constants")
            for dependency in node[field]:
                if dependency in reverse:
                    reverse[dependency][user_field].append(node["name"])
        node["targetReachability"] = [t for t, seen in per_target.items() if node["name"] in seen]
        node.update(reverse[node["name"]])
        node["description"] = by_name.get(node["name"], {}).get("description") or node["docstring"]
        node["descriptionSource"] = ("curated" if node["name"] in by_name else
                                     "Lean docstring" if node["docstring"] else None)
        node["tags"] = by_name.get(node["name"], {}).get("tags", [])
        if node["line"] is not None:
            lines = (ROOT / node["file"]).read_text(encoding="utf-8").splitlines()
            if not 1 <= node["line"] <= len(lines):
                raise ValueError("Invalid Lean source location: " + node["name"])
    # Reverse edges are complete only after every declaration has been visited.
    for node in raw["declarations"]:
        node.update({field: sorted(names) for field, names in reverse[node["name"]].items()})
    hashes_after = {str(p.relative_to(ROOT)): digest(p) for p in source_files}
    if hashes_before != hashes_after:
        raise ValueError("Proof sources changed during extraction; regenerate again")
    manifest = read_json(ROOT / "lake-manifest.json")
    raw.update({
        "schemaVersion": 1,
        "provenance": {
            "dependencies": "Exact constant references in Lean ConstantInfo.type and value? (allowOpaque=true); Expr.foldConsts, after importing the completed solution",
            "proofDepsMeaning": "Stored theorem proof or definition body, including annotations inside that expression; empty for bodyless constructors/inductives/recursors",
            "scope": "Every declaration whose defining module starts QuantumChannelContinuity. or ChannelContinuity.; includes private/generated auxiliaries and unused historical interfaces",
            "externalDependencies": "Direct constants outside project modules remain in typeDeps/proofDeps but have no project node",
            "reachability": "Transitive closure of typeDeps union proofDeps inside indexed project modules; computed separately for each target",
            "locations": "Lean declaration-range extension; null when unavailable, one-based source line",
            "descriptions": "Existing Lean docstrings plus explicitly curated descriptions/tags; these are navigation aids, not mathematical certification",
            "leanToolchain": (ROOT / "lean-toolchain").read_text().strip(),
            "dependencyPins": {p["name"]: p.get("rev") for p in manifest["packages"]},
            "sourceSha256": hashes_after,
            "extractorSha256": digest(ROOT / "scripts" / "ExportProofIndex.lean"),
            "generatorSha256": digest(Path(__file__)),
            "curatedDescriptionsSha256": digest(DESCRIPTIONS),
            "regenerationCommand": "python3 scripts/proof-index.py --regenerate",
        },
        "targets": TARGETS,
        "counts": {
            "declarations": len(nodes),
            "theorems": sum(d["kind"] == "theorem" for d in nodes.values()),
            "withLocations": sum(d["line"] is not None for d in nodes.values()),
            "withDescriptions": sum(bool(d["description"]) for d in nodes.values()),
            "curatedDescriptions": len(by_name),
            "targetClosures": {t: len(seen) for t, seen in per_target.items()},
        },
    })
    write_json(INDEX, raw)
    print("Regenerated docs/proof-index.json: " + str(len(nodes)) + " elaborated declarations.")


def words(text):
    text = re.sub(r"([a-z])([A-Z])", r"\1 \2", text)
    return re.findall(r"[\w]+", text.casefold().replace("_", " "))


def search(index, query, include_all):
    tokens = words(query)
    results = []
    for node in index["declarations"]:
        if not include_all and node["internal"] and not node["description"]:
            continue
        searchable = " ".join([node["displayName"], node["module"],
                               node["description"] or "", " ".join(node["tags"]), node["type"]])
        haystack = " ".join(words(searchable))
        if not all(token in haystack for token in tokens):
            continue
        natural = " ".join(words((node["description"] or "") + " " + " ".join(node["tags"])))
        score = sum(4 if token in natural else 1 for token in tokens)
        name_words = " ".join(words(node["displayName"]))
        score += sum(2 for token in tokens if token in name_words)
        score += 3 if node["descriptionSource"] == "curated" else 0
        score += 1 if node["kind"] == "theorem" else 0
        results.append((score, node))
    return [n for _, n in sorted(results, key=lambda pair: (-pair[0], pair[1]["name"]))]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("query", nargs="?", help="Words in a theorem name, description, tags, or type")
    parser.add_argument("--regenerate", action="store_true", help="Build and extract the pinned completed Lean solution")
    parser.add_argument("--deps", metavar="DECLARATION", help="Show direct type and proof/body dependencies")
    parser.add_argument("--uses", metavar="DECLARATION", help="Show project declarations directly using this declaration")
    parser.add_argument("--closure", metavar="DECLARATION", help="Show the transitive project dependency closure")
    parser.add_argument("--limit", type=int, default=10, help="Maximum search results (default 10)")
    parser.add_argument("--all", action="store_true", help="Include undocumented internal auxiliaries in search")
    parser.add_argument("--json", action="store_true", help="Print machine-readable query results")
    args = parser.parse_args()
    if sys.version_info < (3, 9):
        parser.error("Python 3.9 or newer is required")
    if args.limit < 1:
        parser.error("--limit must be positive")
    if args.regenerate:
        regenerate()
    if not any((args.query, args.deps, args.uses, args.closure)):
        if not args.regenerate:
            parser.print_help()
        return
    index = read_json(INDEX)
    nodes = {n["name"]: n for n in index["declarations"]}
    if args.closure:
        if args.closure not in nodes:
            parser.error("Declaration not found: " + args.closure)
        names = sorted(closure(nodes, [args.closure]))
        result = {"root": args.closure, "count": len(names), "projectDependencies": names}
        if args.json:
            print(json.dumps(result, ensure_ascii=False, indent=2))
        else:
            print(args.closure + ": " + str(len(names)) + " declarations in its project dependency closure")
            for name in names:
                print("  " + name)
        return
    if args.deps or args.uses:
        name = args.deps or args.uses
        if name not in nodes:
            parser.error("Declaration not found: " + name)
        fields = ("typeDeps", "proofDeps") if args.deps else ("typeUsers", "proofUsers")
        result = {"name": name, **{f: nodes[name][f] for f in fields}}
        if args.json:
            print(json.dumps(result, ensure_ascii=False, indent=2))
        else:
            print(name)
            for field in fields:
                print(field + ":")
                for dependency in result[field]:
                    print("  " + dependency)
        return
    matches = search(index, args.query, args.all)[:args.limit]
    if args.json:
        print(json.dumps(matches, ensure_ascii=False, indent=2))
    else:
        if not matches:
            print("No matching declarations.")
        for node in matches:
            location = node["file"] + (":" + str(node["line"]) if node["line"] else "")
            print(node["name"] + "\n  " + location)
            description = node["description"] or node["type"]
            print("  " + " ".join(description.split()))
            if node["tags"]:
                print("  Tags: " + ", ".join(node["tags"]))
            print()


if __name__ == "__main__":
    main()
