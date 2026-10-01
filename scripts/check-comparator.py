#!/usr/bin/env python3
# Copyright (c) 2026 Jinzhao Wang. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Jinzhao Wang (AI-assisted formalization)

"""Reproduce Comparator statement, axiom, and Lean kernel checks locally.

Uses the pinned upstream development launcher, which provides no sandbox.
The independent nanoda replay is documented separately in VERIFYING.md.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent
PINS = {
    "Comparator": "066c3bc9e966ccad9a633d780ae4de13cd0f27b6",
    "Lean4Checker": "b7398199245524275543dec6113229c9bb4902e5",
    "lean4export": "048394e1afeeb52b0fa27bcf3f1ade2ff0f0ab6d",
}
SHIM_SHA = "167507c89d8b3c7667ad78b50df7b19f89883751a01efd1457404fa34a994e8b"
TARGETS = [
    "QuantumChannelContinuity.theorem_one",
    "QuantumChannelContinuity.blockRenyi_tendsto_regularized",
    "QuantumChannelContinuity.blockRelative_tendsto_regularized",
]
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources():
    paths = list(ROOT.glob("*.lean"))
    for directory in ("ChannelContinuity", "QuantumChannelContinuity", "ComparatorChallenges"):
        paths.extend((ROOT / directory).rglob("*.lean"))
    paths.extend((ROOT / "ComparatorChallenges").glob("*.json"))
    paths.extend(ROOT / name for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"))
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-cache", action="store_true",
                        help="Skip downloading mathlib caches when dependencies are already prepared.")
    args = parser.parse_args()
    if sys.version_info < (3, 9):
        parser.error("Python 3.9 or newer is required")

    stamp = datetime.now(timezone.utc)
    output = ROOT / ".lake" / "comparator-check" / stamp.strftime("%Y%m%dT%H%M%S.%fZ")
    output.mkdir(parents=True)
    report = {
        "status": "FAIL",
        "started_utc": stamp.isoformat(),
        "sandbox": "none: upstream development launcher",
        "nanoda": "not run; see VERIFYING.md for independent replay",
        "tool_pins": PINS,
        "theorems": TARGETS,
        "permitted_axioms": AXIOMS,
        "checks": [],
    }
    env = os.environ.copy()
    if sys.platform == "darwin" and Path("/Library/Developer/CommandLineTools").is_dir():
        env["DEVELOPER_DIR"] = "/Library/Developer/CommandLineTools"
    before = sources()
    (output / "source-sha256.json").write_text(json.dumps(before, indent=2) + "\n")

    def run(name, arguments):
        print("Running " + name + "…", flush=True)
        log_path = output / (name + ".log")
        with log_path.open("w") as log:
            result = subprocess.run(["./run-lake.sh", *arguments], cwd=ROOT, env=env,
                                    stdout=log, stderr=subprocess.STDOUT)
        return result.returncode, log_path.read_text(errors="replace")

    try:
        print("Comparator reproduction: UNSANDBOXED development mode", flush=True)
        print("Logs: " + str(output), flush=True)
        for name in ("ChannelRenyiContinuity", "WrongStatement", "MissingProof"):
            config = json.loads((ROOT / "ComparatorChallenges" / (name + ".json")).read_text())
            expected_targets = TARGETS if name == "ChannelRenyiContinuity" else TARGETS[:1]
            if (config["theorem_names"] != expected_targets
                    or set(config["permitted_axioms"]) != set(AXIOMS)
                    or config.get("enable_nanoda") is not False):
                raise RuntimeError("Unexpected targets, axioms, or kernel configuration: " + name)
        if not args.skip_cache:
            code, _ = run("cache", ["exe", "cache", "get"])
            if code:
                raise RuntimeError("Dependency cache setup failed; see cache.log.")
        code, _ = run("build-tools", ["build", "comparator", "lean4export"])
        if code:
            raise RuntimeError("Checker build failed; see build-tools.log. Install elan if lake is missing.")

        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        revisions = {p["name"]: p["rev"] for p in manifest["packages"]}
        for name, expected in PINS.items():
            package = ROOT / ".lake" / "packages" / name
            actual = subprocess.check_output(["git", "-C", str(package), "rev-parse", "HEAD"],
                                             env=env, text=True).strip()
            if revisions.get(name) != expected or actual != expected:
                raise RuntimeError("Unexpected checker revision: " + name)
            for command in (["diff", "--quiet"], ["diff", "--cached", "--quiet"]):
                subprocess.run(["git", "-C", str(package), *command], env=env, check=True)

        shim = ROOT / "scripts" / "comparator-development-landrun.sh"
        if digest(shim) != SHIM_SHA:
            raise RuntimeError("The pinned development launcher checksum does not match.")
        binaries = output / "bin"
        binaries.mkdir()
        (binaries / "landrun").symlink_to(shim)
        env["PATH"] = str(binaries) + os.pathsep + env.get("PATH", "")

        jobs = [
            ("positive", "ChannelRenyiContinuity", True,
             ["Lean default kernel accepts the solution", "Your solution is okay!"]),
            ("wrong-statement", "WrongStatement", False,
             ["Challenge and solution theorem statement do not match"]),
            ("missing-proof", "MissingProof", False,
             ["Illegal axiom detected: 'sorryAx'"]),
        ]
        for name, config, expect_success, diagnostics in jobs:
            config_path = "ComparatorChallenges/" + config + ".json"
            code, log = run(name, ["env", "comparator", config_path])
            passed = ((code == 0) == expect_success and all(s in log for s in diagnostics))
            report["checks"].append({
                "name": name, "configuration": config_path,
                "configuration_sha256": digest(ROOT / config_path),
                "exit_status": code, "expected_success": expect_success,
                "expected_diagnostics": diagnostics, "passed": passed,
                "log": name + ".log", "log_sha256": digest(output / (name + ".log")),
            })
            if not passed:
                raise RuntimeError("Unexpected result for " + name + "; see " + name + ".log.")
            print("PASS: " + name, flush=True)

        report["proof_sources_unchanged"] = sources() == before
        if not report["proof_sources_unchanged"]:
            raise RuntimeError("Proof sources or checker configurations changed during checking.")
        report["status"] = "PASS"
    except Exception as error:
        report["error"] = str(error)
        print("FAIL: " + str(error), file=sys.stderr)
    finally:
        (output / "result.json").write_text(json.dumps(report, indent=2) + "\n")
    if report["status"] != "PASS":
        return 1
    print("COMPARATOR CHECK PASSED: three theorem targets, Lean kernel replay, and both rejection controls.")
    print("Result: " + str(output / "result.json"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
