#!/usr/bin/env python3
# Copyright (c) 2026 Jinzhao Wang. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Jinzhao Wang (AI-assisted formalization)

"""Build, export, and independently check the current proof with pinned Nanoda."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import runpy
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent
shared = runpy.run_path(str(ROOT / "scripts" / "check-comparator.py"))
TARGETS = shared["TARGETS"]
AXIOMS = shared["AXIOMS"]
sources = shared["sources"]
NANODA_PIN = "3a2407216ee84a75f9e1aead6803d0578be06ae7"
EXPORTER_PIN = shared["PINS"]["lean4export"]
KERNEL_DECLS = [
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod",
    "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft",
    "Nat.shiftRight", "String.ofList",
]


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-cache", action="store_true",
                        help="Skip downloading mathlib caches when dependencies are already prepared.")
    args = parser.parse_args()
    if sys.version_info < (3, 9):
        parser.error("Python 3.9 or newer is required")
    started = datetime.now(timezone.utc)
    output = ROOT / ".lake" / "nanoda-check" / started.strftime("%Y%m%dT%H%M%S.%fZ")
    output.mkdir(parents=True)
    report = {
        "status": "FAIL", "started_utc": started.isoformat(),
        "checker_commit": NANODA_PIN, "exporter_commit": EXPORTER_PIN,
        "theorems": TARGETS, "permitted_axioms": AXIOMS,
        "input": "fresh export of ChannelRenyiContinuity from this checkout",
    }
    env = os.environ.copy()
    if sys.platform == "darwin" and Path("/Library/Developer/CommandLineTools").is_dir():
        env["DEVELOPER_DIR"] = "/Library/Developer/CommandLineTools"
    before = sources()
    (output / "source-sha256.json").write_text(json.dumps(before, indent=2) + "\n")

    def run(name, command):
        print("Running " + name + "…", flush=True)
        with (output / (name + ".log")).open("w") as log:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(name + " failed with exit status " + str(result.returncode)
                               + "; see " + name + ".log.")

    try:
        print("Independent Nanoda reproduction", flush=True)
        print("Logs and exported proof: " + str(output), flush=True)
        if not args.skip_cache:
            run("cache", ["./run-lake.sh", "exe", "cache", "get"])
        run("build-proof", ["./run-lake.sh", "build", "All", "lean4export"])
        exporter = ROOT / ".lake" / "packages" / "lean4export"
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        revisions = {p["name"]: p["rev"] for p in manifest["packages"]}
        actual = subprocess.check_output(["git", "-C", str(exporter), "rev-parse", "HEAD"],
                                         env=env, text=True).strip()
        if revisions.get("lean4export") != EXPORTER_PIN or actual != EXPORTER_PIN:
            raise RuntimeError("Unexpected exporter revision.")
        for diff in (["diff", "--quiet"], ["diff", "--cached", "--quiet"]):
            subprocess.run(["git", "-C", str(exporter), *diff], env=env, check=True)

        run("build-nanoda", ["bash", "scripts/bootstrap-nanoda.sh"])
        checker = ROOT / ".lake" / "nanoda-tools" / "nanoda_lib"
        actual = subprocess.check_output(["git", "-C", str(checker), "rev-parse", "HEAD"],
                                         env=env, text=True).strip()
        if actual != NANODA_PIN:
            raise RuntimeError("Unexpected Nanoda revision.")
        binary = checker / "target" / "release" / "nanoda_bin"
        report["checker_binary_sha256"] = digest(binary)

        export = output / "Solution.ndjson"
        print("Exporting the three theorem targets…", flush=True)
        command = ["./run-lake.sh", "env", "lean4export", "ChannelRenyiContinuity", "--",
                   *TARGETS, *AXIOMS, *KERNEL_DECLS]
        with export.open("wb") as proof, (output / "export.log").open("wb") as log:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=proof, stderr=log)
        if result.returncode:
            raise RuntimeError("Proof export failed; see export.log.")
        report["export_sha256"] = digest(export)
        report["export_bytes"] = export.stat().st_size
        rendered = output / "theorems.txt"
        rendered.write_text("")
        config = {
            "export_file_path": str(export), "use_stdin": False,
            "permitted_axioms": AXIOMS,
            "unpermitted_axiom_hard_error": True, "unsafe_permit_all_axioms": False,
            "num_threads": 1, "nat_extension": True, "string_extension": True,
            "pp_declars": TARGETS, "unknown_pp_declar_hard_error": True,
            "pp_options": {"proofs": False, "width": 100},
            "pp_output_path": str(rendered), "pp_to_stdout": False,
            "print_axioms": True, "print_success_message": True,
        }
        config_path = output / "nanoda-config.json"
        config_path.write_text(json.dumps(config, indent=2) + "\n")
        report["configuration_sha256"] = digest(config_path)
        run("nanoda", [str(binary), str(config_path)])
        log = (output / "nanoda.log").read_text()
        match = re.search(r"Checked (\d+) declarations with no errors", log)
        if match is None:
            raise RuntimeError("Nanoda did not report successful proof checking.")
        report["checked_declarations"] = int(match.group(1))
        report["log_sha256"] = digest(output / "nanoda.log")
        report["export_unchanged"] = digest(export) == report["export_sha256"]
        report["proof_sources_unchanged"] = sources() == before
        if not report["export_unchanged"] or not report["proof_sources_unchanged"]:
            raise RuntimeError("Proof export or sources changed during verification.")
        report["status"] = "PASS"
    except Exception as error:
        report["error"] = str(error)
        print("FAIL: " + str(error), file=sys.stderr)
    finally:
        (output / "result.json").write_text(json.dumps(report, indent=2) + "\n")
    if report["status"] != "PASS":
        return 1
    print("NANODA CHECK PASSED: " + str(report["checked_declarations"])
          + " declarations; three theorem targets.")
    print("Result: " + str(output / "result.json"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
