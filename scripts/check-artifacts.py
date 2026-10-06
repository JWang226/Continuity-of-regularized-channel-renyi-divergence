#!/usr/bin/env python3
# Copyright (c) 2026 Jinzhao Wang. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Jinzhao Wang (AI-assisted formalization)

"""Check publication metadata and provenance; requires Python 3.9+ only.

This validates artifact consistency, not mathematical correspondence. Optional
dependency source hashes are checked when Lake has installed those sources.
"""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
TARGETS = {
    "QuantumChannelContinuity.theorem_one",
    "QuantumChannelContinuity.blockRenyi_tendsto_regularized",
    "QuantumChannelContinuity.blockRelative_tendsto_regularized",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(name):
    return json.loads((ROOT / name).read_text(encoding="utf-8"))


def local_path(name):
    path = Path(name)
    require(not path.is_absolute() and ".." not in path.parts,
            "Nonportable artifact path: " + name)
    return ROOT / path


def check_hash(name, expected, optional_dependency=False):
    path = local_path(name)
    if optional_dependency and name.startswith(".lake/packages/") and not path.exists():
        return False
    require(path.is_file(), "Missing artifact input: " + name)
    require(digest(path) == expected, "Stale artifact hash: " + name)
    return True


def main():
    require(sys.version_info >= (3, 9), "Python 3.9+ is required")
    lean_files = list(ROOT.glob("*.lean"))
    for directory in ("ChannelContinuity", "QuantumChannelContinuity", "ComparatorChallenges", "scripts"):
        lean_files.extend((ROOT / directory).rglob("*.lean"))
    for path in lean_files:
        text = path.read_text(encoding="utf-8")[:2000].lower()
        require("copyright" in text and "apache" in text,
                "Missing copyright/license header: " + str(path.relative_to(ROOT)))
    for path in [*ROOT.glob("*.sh"), *(ROOT / "scripts").glob("*.sh"), *(ROOT / "scripts").glob("*.py")]:
        if path.name == "comparator-development-landrun.sh":
            continue  # Unmodified, checksum-pinned third-party launcher.
        require("copyright" in path.read_text(encoding="utf-8")[:1500].lower(),
                "Missing script notice: " + str(path.relative_to(ROOT)))

    historical = load("Verification/source-identity.json")
    current = load("Verification/current-source-identity.json")
    old_hashes = {r["path"]: r["sha256"] for r in historical["files"]}
    require({r["path"] for r in current["files"]} == set(old_hashes), "Historical source inventory differs")
    header = current["added_header"].encode("utf-8")
    for record in current["files"]:
        data = local_path(record["path"]).read_bytes()
        require(hashlib.sha256(data).hexdigest() == record["sha256"], "Current source hash differs: " + record["path"])
        if record["added_project_header"]:
            require(data.startswith(header), "Recorded added header differs: " + record["path"])
            data = data[len(header):]
        require(hashlib.sha256(data).hexdigest() == old_hashes[record["path"]]
                == record["historical_sha256"], "More than a header changed: " + record["path"])

    mapping = load("docs/paper-mapping.json")
    require(mapping["paper"]["id"] == "arXiv:2609.28635v1", "Unexpected paper version")
    check_hash(mapping["snapshot"]["file"], mapping["snapshot"]["sha256"])
    manuscript = local_path(mapping["snapshot"]["file"]).read_text(encoding="utf-8")
    index = load("docs/proof-index.json")
    nodes = {node["name"]: node for node in index["declarations"]}
    require(len(nodes) == index["counts"]["declarations"], "Index count differs")
    require(set(index["targets"]) == TARGETS, "Index targets differ")
    provenance = index["provenance"]
    for name, value in provenance["sourceSha256"].items():
        check_hash(name, value)
    for name, field in [("scripts/ExportProofIndex.lean", "extractorSha256"),
                        ("scripts/proof-index.py", "generatorSha256"),
                        ("docs/lemma-descriptions.json", "curatedDescriptionsSha256")]:
        check_hash(name, provenance[field])
    mapped = set()
    for entry in mapping["entries"]:
        for label in entry["natural_language"]["latex_labels"]:
            require("\\label{" + label + "}" in manuscript, "Unknown paper label: " + label)
        for target in entry["formal"]:
            name = target["declaration"]
            require(name in nodes and nodes[name]["file"] == target["file"], "Unknown formal mapping: " + name)
            mapped.add(name)
    require(TARGETS <= mapped, "A main theorem has no paper mapping")
    for entry in mapping["outside_scope"]:
        require(entry["status"] == "outside-formalization-scope", "Ambiguous excluded-result status")
        require("\\label{" + entry["latex_label"] + "}" in manuscript, "Unknown excluded-result label")
    for node in nodes.values():
        require(local_path(node["file"]).exists(), "Unknown declaration file: " + node["file"])
        for field, reverse in [("typeDeps", "typeUsers"), ("proofDeps", "proofUsers")]:
            for dep in node[field]:
                if dep in nodes:
                    require(node["name"] in nodes[dep][reverse], "Inconsistent dependency edge: " + node["name"])

    readback = load("docs/lean-readback.json")
    require(readback["status"] == "agent-readback-not-human-review"
            and readback["human_review_completed"] is False
            and readback["method"]["prohibited_material_consulted"] is False,
            "Read-back provenance/status differs")
    require({r["formal_name"] for r in readback["declarations"]} == TARGETS, "Read-back targets differ")
    skipped = 0
    for record in readback["input_files"]:
        skipped += not check_hash(record["path"], record["sha256"], optional_dependency=True)
    comparison = load("docs/paper-comparison.json")
    require(comparison["human_review_completed"] is False, "Human review cannot be inferred from agent checks")
    for name, expected in comparison["input_sha256"].items():
        check_hash(name, expected)
    for name, expected in comparison["supporting_signature_source_sha256"].items():
        check_hash(name, expected)
    config = load("ComparatorChallenges/ChannelRenyiContinuity.json")
    require(set(config["theorem_names"]) == TARGETS, "Comparator targets differ")
    require(set(config["permitted_axioms"]) == {"propext", "Classical.choice", "Quot.sound"}, "Comparator axiom policy differs")
    metadata = (ROOT / "formalization.yaml").read_text(encoding="utf-8")
    require('id: "arXiv:2609.28635v1"' in metadata, "Stale paper identifier in formalization.yaml")
    for target in TARGETS:
        require('declaration: "' + target + '"' in metadata, "Missing YAML result: " + target)
    statement_audit = load("docs/statement-audit.json")
    require(statement_audit["human_review_completed"] is False
            and statement_audit["status"] == "scope-qualified-agent-audit",
            "Statement audit review status differs")
    require({r["declaration"] for r in statement_audit["targets"]} == TARGETS,
            "Statement audit targets differ")
    for record in statement_audit["input_files"]:
        skipped += not check_hash(record["path"], record["sha256"], optional_dependency=True)
    for target in statement_audit["targets"]:
        lines = local_path(target["file"]).read_bytes().splitlines(keepends=True)
        for field in ("signature", "declaration_source"):
            loc = target[field]
            data = b"".join(lines[loc["start_line"] - 1:loc["end_line"]])
            require(hashlib.sha256(data).hexdigest() == loc["sha256"],
                    "Statement audit declaration range differs: " + target["declaration"])
    candidate = load("Contributions/Physlib/trace-power-derivative.json")
    check_hash(candidate["patch"]["path"], candidate["patch"]["sha256"])
    check_hash(candidate["evidence_file"], candidate["evidence_sha256"])
    require(candidate["submitted_upstream"] is False and candidate["human_review_completed"] is False,
            "Upstream review/submission cannot be inferred from local checks")
    print("ARTIFACT CHECK PASSED: " + str(len(lean_files)) + " Lean headers; "
          + str(len(current["files"])) + " historical proof sources; "
          + str(len(mapping["entries"])) + " paper mappings; " + str(len(nodes)) + " indexed declarations.")
    if skipped:
        print(str(skipped) + " dependency source hashes skipped; install Lake dependencies to check them too.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, KeyError, OSError) as error:
        print("ARTIFACT CHECK FAILED: " + str(error), file=sys.stderr)
        sys.exit(1)
