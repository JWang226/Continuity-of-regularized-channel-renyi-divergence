#!/usr/bin/env python3
# Copyright (c) 2026 Jinzhao Wang. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Jinzhao Wang (AI-assisted formalization)

"""Bind current sources and verify retained historical audit inputs.

Refresh with ``python3 scripts/source_provenance.py --refresh`` after an
intentional source change. Refreshing hashes is bookkeeping, not a proof check
or a new assessment of correspondence to the paper. Python 3.9+ only.
"""
import hashlib
import json
from pathlib import Path
import sys
import zipfile

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = "Verification/source-snapshots/pre-cleanup-2026-10-06.json"
IDENTITY = "Verification/current-source-identity.json"
SOURCE_DIRS = ("ChannelContinuity", "QuantumChannelContinuity", "ComparatorChallenges", "scripts")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def local_path(name):
    path = Path(name)
    require(not path.is_absolute() and ".." not in path.parts,
            "Nonportable artifact path: " + name)
    return ROOT / path


def lean_paths():
    paths = set(ROOT.glob("*.lean"))
    for directory in SOURCE_DIRS:
        paths.update((ROOT / directory).rglob("*.lean"))
    return sorted(str(path.relative_to(ROOT)) for path in paths if path.is_file())


def checker_inputs():
    paths = set(ROOT.glob("*.sh"))
    paths.update((ROOT / "scripts").rglob("*.py"))
    paths.update((ROOT / "scripts").rglob("*.sh"))
    paths.update((ROOT / "ComparatorChallenges").glob("*.json"))
    paths.update(ROOT / name for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"))
    return sorted(str(path.relative_to(ROOT)) for path in paths if path.is_file())


def load_snapshot():
    manifest_data = local_path(MANIFEST).read_bytes()
    manifest = json.loads(manifest_data)
    require(manifest["schema"] == "retained-source-snapshot-v1", "Unexpected historical snapshot schema")
    archive = local_path(manifest["archive"]["path"])
    require(sha256(archive.read_bytes()) == manifest["archive"]["sha256"], "Historical snapshot archive hash differs")
    require(archive.stat().st_size == manifest["archive"]["bytes"], "Historical snapshot archive size differs")
    records = {record["path"]: record for record in manifest["files"]}
    require(len(records) == len(manifest["files"]), "Duplicate historical snapshot record")
    with zipfile.ZipFile(archive) as zipped:
        require(len(zipped.namelist()) == len(set(zipped.namelist())), "Duplicate historical snapshot member")
        require(set(zipped.namelist()) == set(records), "Historical snapshot inventory differs")
        content = {}
        for name, record in records.items():
            local_path(name)  # Validate portability without extracting the archive.
            data = zipped.read(name)
            require(len(data) == record["bytes"] and sha256(data) == record["sha256"],
                    "Historical snapshot member differs: " + name)
            content[name] = data
    return manifest, content, sha256(manifest_data)


def verify_historical_identity(content):
    historical_name = "Verification/source-identity.json"
    require(local_path(historical_name).read_bytes() == content[historical_name],
            "Historical certificate source mapping changed")
    historical = json.loads(content[historical_name])
    original = json.loads(content[IDENTITY])
    require(original["schema"] == "current-source-identity-v1", "Expected archived header-only source identity")
    old_hashes = {record["path"]: record["sha256"] for record in historical["files"]}
    require({record["path"] for record in original["files"]} == set(old_hashes),
            "Archived historical source inventory differs")
    header = original["added_header"].encode("utf-8")
    for record in original["files"]:
        data = content[record["path"]]
        require(sha256(data) == record["sha256"], "Archived pre-cleanup source differs: " + record["path"])
        if record["added_project_header"]:
            require(data.startswith(header), "Archived added header differs: " + record["path"])
            data = data[len(header):]
        require(sha256(data) == old_hashes[record["path"]] == record["historical_sha256"],
                "Archived source changed beyond the added header: " + record["path"])
    return historical, original


def historical_bytes(name, expected=None, snapshot=None):
    """Read an old assessment's input from its retained snapshot, never reassign it."""
    if snapshot is None:
        _, snapshot, _ = load_snapshot()
    require(name in snapshot, "Historical audit input not retained: " + name)
    data = snapshot[name]
    if expected is not None:
        require(sha256(data) == expected, "Historical audit input hash differs: " + name)
    return data


def verify_current_identity():
    manifest, content, manifest_hash = load_snapshot()
    historical, original = verify_historical_identity(content)
    current = json.loads(local_path(IDENTITY).read_text(encoding="utf-8"))
    require(current["schema"] == "current-source-identity-v2", "Current source identity needs a v2 refresh")
    require(current["historical_mapping"] == "Verification/source-identity.json"
            and current["historical_certificate_sha256"] == historical["historical_certificate_sha256"]
            and current["historical_public_commit"] == original["baseline_public_commit"],
            "Historical certificate provenance differs")
    require(current["retained_baseline"]["manifest"] == MANIFEST
            and current["retained_baseline"]["manifest_sha256"] == manifest_hash
            and current["retained_baseline"]["repository_commit"] == manifest["repository_commit"],
            "Retained baseline provenance differs")
    actual_paths = set(lean_paths())
    records = {record["path"]: record for record in current["files"]}
    require(len(records) == len(current["files"]) and set(records) == actual_paths,
            "Current owned Lean source inventory differs; refresh provenance after intentional changes")
    require(current["source_file_count"] == len(records), "Current source count differs")
    old_hashes = {record["path"]: record["sha256"] for record in historical["files"]}
    for name, record in records.items():
        require(sha256(local_path(name).read_bytes()) == record["sha256"], "Current source hash differs: " + name)
        expected_baseline = sha256(content[name]) if name in content else None
        require(record["baseline_sha256"] == expected_baseline
                and record["historical_sha256"] == old_hashes.get(name), "Recorded source relationship differs: " + name)
        classification = "added" if expected_baseline is None else (
            "unchanged" if expected_baseline == record["sha256"] else "modified")
        require(record["change"] == classification, "Source change classification differs: " + name)
    baseline_paths = {name for name in content if name.endswith(".lean") and
                      (len(Path(name).parts) == 1 or Path(name).parts[0] in SOURCE_DIRS)}
    removed = {record["path"]: record for record in current["removed_files"]}
    require(len(removed) == len(current["removed_files"]) and set(removed) == baseline_paths - actual_paths,
            "Removed source inventory differs")
    for name, record in removed.items():
        require(not local_path(name).exists() and record["baseline_sha256"] == sha256(content[name])
                and record["historical_sha256"] == old_hashes.get(name), "Removed source record differs: " + name)
    inputs = {record["path"]: record for record in current["checker_inputs"]}
    require(len(inputs) == len(current["checker_inputs"]) and set(inputs) == set(checker_inputs()),
            "Current checker input inventory differs")
    for name, record in inputs.items():
        require(sha256(local_path(name).read_bytes()) == record["sha256"], "Current checker input hash differs: " + name)
    require(current["all_changes_are_headers_only"] is False,
            "A later proof cleanup cannot be represented as the historical header-only snapshot")
    return current, content


def refresh():
    manifest, content, manifest_hash = load_snapshot()
    historical, original = verify_historical_identity(content)
    old_hashes = {record["path"]: record["sha256"] for record in historical["files"]}
    current_paths = lean_paths()
    baseline_paths = {name for name in content if name.endswith(".lean") and
                      (len(Path(name).parts) == 1 or Path(name).parts[0] in SOURCE_DIRS)}
    files = []
    for name in current_paths:
        digest = sha256(local_path(name).read_bytes())
        baseline = sha256(content[name]) if name in content else None
        files.append({"path": name, "sha256": digest, "baseline_sha256": baseline,
                      "historical_sha256": old_hashes.get(name),
                      "change": "added" if baseline is None else ("unchanged" if digest == baseline else "modified")})
    current = {
        "schema": "current-source-identity-v2",
        "historical_mapping": "Verification/source-identity.json",
        "historical_certificate_sha256": historical["historical_certificate_sha256"],
        "historical_public_commit": original["baseline_public_commit"],
        "retained_baseline": {"repository_commit": manifest["repository_commit"], "manifest": MANIFEST,
                              "manifest_sha256": manifest_hash},
        "policy": "Historical certificates and dated assessments retain their original inputs in the baseline archive. Later cleanup sources are hashed here and require fresh proof checks; this identity record is not a certificate or semantic review.",
        "all_changes_are_headers_only": False,
        "source_file_count": len(files),
        "files": files,
        "removed_files": [{"path": name, "baseline_sha256": sha256(content[name]),
                           "historical_sha256": old_hashes.get(name)} for name in sorted(baseline_paths - set(current_paths))],
        "checker_inputs": [{"path": name, "sha256": sha256(local_path(name).read_bytes())}
                           for name in checker_inputs()],
    }
    local_path(IDENTITY).write_text(json.dumps(current, indent=2) + "\n", encoding="utf-8")
    verify_current_identity()
    print("CURRENT SOURCE IDENTITY REFRESHED: " + str(len(files)) + " owned Lean files; "
          + str(len(current["removed_files"])) + " removed baseline paths. Fresh proof checks are still required.")


if __name__ == "__main__":
    try:
        require(sys.version_info >= (3, 9), "Python 3.9+ is required")
        if sys.argv[1:] == ["--refresh"]:
            refresh()
        elif not sys.argv[1:]:
            current, _ = verify_current_identity()
            print("SOURCE PROVENANCE PASSED: " + str(len(current["files"])) + " current Lean sources; historical inputs retained separately.")
        else:
            raise ValueError("Usage: python3 scripts/source_provenance.py [--refresh]")
    except (ValueError, KeyError, OSError, zipfile.BadZipFile) as error:
        print("SOURCE PROVENANCE FAILED: " + str(error), file=sys.stderr)
        sys.exit(1)
