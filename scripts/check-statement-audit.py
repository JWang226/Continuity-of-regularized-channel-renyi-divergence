#!/usr/bin/env python3
# Copyright (c) 2026 Jinzhao Wang. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Jinzhao Wang (AI-assisted formalization)

"""Recheck audit input hashes and compile exact-type/definition probes.

This reproduces the mechanical evidence. It does not automate the comparison
between the paper and Lean or supply independent human review. Python 3.9+.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

from source_provenance import historical_bytes, verify_current_identity

ROOT = Path(__file__).resolve().parent.parent
TARGETS = (
    "QuantumChannelContinuity.theorem_one",
    "QuantumChannelContinuity.blockRenyi_tendsto_regularized",
    "QuantumChannelContinuity.blockRelative_tendsto_regularized",
)
PERMITTED = {"propext", "Classical.choice", "Quot.sound"}

PROBES = """import ChannelRenyiContinuity
import QuantumChannelContinuity.SourceCorrespondence
open QuantumState QuantumChannel Filter Set
open scoped ComplexOrder TensorProduct ENNReal Topology
namespace QuantumChannelContinuity
variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]

example (N M : CPTP H K) :
    Tendsto (fun α : ℝ => regularizedRenyi α N M) (𝓝[≠] (1 : ℝ))
      (𝓝 (regularizedRelative N M)) := theorem_one N M

example {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1) (N M : CPTP H K) :
    Tendsto (fun n : ℕ => blockRenyi p N M n / (n : ℝ≥0∞)) atTop
      (𝓝 (regularizedRenyi p N M)) := blockRenyi_tendsto_regularized hp hp1 N M

example (N M : CPTP H K) :
    Tendsto (fun n : ℕ => blockRelative N M n / (n : ℝ≥0∞)) atTop
      (𝓝 (regularizedRelative N M)) := blockRelative_tendsto_regularized N M

example {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1) (N M : CPTP H K) :
    channelRenyi p N M =
      ⨆ ψ : PureInput (H ⊗[ℂ] H),
        (stateRenyi p (referenceFirstOutput N ψ.density)
          (referenceFirstOutput M ψ.density)).toENNReal :=
  channelRenyi_eq_referenceFirst hp hp1 N M

example (N M : CPTP H K) :
    channelRelative N M =
      ⨆ ψ : PureInput (H ⊗[ℂ] H),
        (stateRelative (referenceFirstOutput N ψ.density)
          (referenceFirstOutput M ψ.density)).toENNReal :=
  channelRelative_eq_referenceFirst N M

example (p : ℝ) (N M : CPTP H K) :
    regularizedRenyi p N M =
      ⨆ n : ℕ, ⨆ (_ : 0 < n), blockRenyi p N M n / (n : ℝ≥0∞) := rfl

example (N M : CPTP H K) :
    regularizedRelative N M =
      ⨆ n : ℕ, ⨆ (_ : 0 < n), blockRelative N M n / (n : ℝ≥0∞) := rfl

example {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1) (ρ σ : DensityState H) :
    ((stateRenyi p ρ σ).toENNReal : EReal) = stateRenyi p ρ σ :=
  EReal.coe_toENNReal (stateRenyi_nonneg hp hp1 ρ σ)

example (ρ σ : DensityState H) :
    ((stateRelative ρ σ).toENNReal : EReal) = stateRelative ρ σ :=
  EReal.coe_toENNReal (stateRelative_nonneg ρ σ)

example : ∀ᶠ α : ℝ in 𝓝[≠] (1 : ℝ), 1 / 2 ≤ α ∧ α ≠ 1 := by
  have h : ∀ᶠ α : ℝ in 𝓝[≠] (1 : ℝ), 1 / 2 < α :=
    (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [h, self_mem_nhdsWithin] with α hα hne
  exact ⟨hα.le, by simpa using hne⟩
end QuantumChannelContinuity

#print QuantumState.Qudit
#print QuantumChannel.CPTP
#print CompletelyPositiveMap
#print Nontrivial
#print QuantumChannelContinuity.DensityState
#print QuantumChannelContinuity.PureInput
#print QuantumChannelContinuity.regularizedRenyi
#print QuantumChannelContinuity.regularizedRelative
#print axioms QuantumChannelContinuity.theorem_one
#print axioms QuantumChannelContinuity.blockRenyi_tendsto_regularized
#print axioms QuantumChannelContinuity.blockRelative_tendsto_regularized
#print axioms QuantumChannelContinuity.referenceFirstOutput_swap
#print axioms QuantumChannelContinuity.channelRenyi_eq_referenceFirst
#print axioms QuantumChannelContinuity.channelRelative_eq_referenceFirst
"""


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def check_inputs(report, snapshot):
    for record in report["input_files"]:
        historical_bytes(record["path"], record["sha256"], snapshot)
    if sha256(PROBES.encode("utf-8")) != report["mechanical_checks"]["probe_sha256"]:
        raise ValueError("Probe source differs from the recorded audit")


def dependency_inputs(report):
    """Bind live inputs of fresh probes independently of the historical snapshot."""
    hashes = {}
    packages = set()
    for record in report["input_files"]:
        name = record["path"]
        if not name.startswith(".lake/packages/"):
            continue
        source = ROOT / name
        if not source.is_file():
            raise ValueError("Missing live dependency input needed by current probes: " + name)
        actual = sha256(source.read_bytes())
        if actual != record["sha256"]:
            raise ValueError("Live dependency source differs from the audited pinned input: " + name)
        hashes[name] = actual
        packages.add(Path(name).parts[2])
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    pins = {package["name"]: package["rev"] for package in manifest["packages"]
            if "rev" in package}
    env = os.environ.copy()
    if sys.platform == "darwin" and Path("/Library/Developer/CommandLineTools").is_dir():
        env["DEVELOPER_DIR"] = "/Library/Developer/CommandLineTools"
    revisions = {}
    for name in sorted(packages):
        checkout = ROOT / ".lake" / "packages" / name
        actual = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"],
                                         env=env, text=True).strip()
        if name not in pins or actual != pins[name]:
            raise ValueError("Live dependency revision differs from manifest pin: " + name)
        for arguments in (["diff", "--quiet"], ["diff", "--cached", "--quiet"]):
            result = subprocess.run(["git", "-C", str(checkout), *arguments], env=env,
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            if result.returncode:
                raise ValueError("Live dependency has tracked changes or could not be checked: " + name)
        revisions[name] = {"actual_head": actual, "manifest_pin": pins[name],
                           "tracked_worktree_clean": True}
    return {"source_sha256": hashes, "package_revisions": revisions}


def run():
    if sys.version_info < (3, 9):
        raise ValueError("Python 3.9+ is required")
    if sys.argv[1:] not in ([], ["--hashes-only"]):
        raise ValueError("Usage: python3 scripts/check-statement-audit.py [--hashes-only]")
    logdir = ROOT / ".lake" / "statement-audit"
    logdir.mkdir(parents=True, exist_ok=True)
    if not sys.argv[1:]:
        # A failed or interrupted full rerun must not leave an earlier PASS.
        (logdir / "result.json").unlink(missing_ok=True)
    current, snapshot = verify_current_identity()
    report_path = ROOT / "docs/statement-audit.json"
    if report_path.read_bytes() != snapshot["docs/statement-audit.json"]:
        raise ValueError("The dated historical statement assessment was rewritten")
    report = json.loads(report_path.read_text(encoding="utf-8"))
    check_inputs(report, snapshot)
    before = {record["path"]: record["sha256"] for record in current["files"]}
    before.update({record["path"]: record["sha256"] for record in current["checker_inputs"]})
    if sys.argv[1:] == ["--hashes-only"]:
        print("STATEMENT AUDIT INPUT HASHES PASSED: retained historical assessment and current source identity; no fresh Lean run")
        return
    dependencies = dependency_inputs(report)
    with (logdir / "build.log").open("w", encoding="utf-8") as output:
        subprocess.run([str(ROOT / "run-lake.sh"), "build", "ChannelRenyiContinuity",
                        "QuantumChannelContinuity.SourceCorrespondence"],
                       cwd=ROOT, stdout=output, stderr=subprocess.STDOUT, check=True)
    # No tracked candidate declaration: remove the temporary source after checking.
    with tempfile.TemporaryDirectory(prefix="probe-", dir=logdir) as temporary:
        source = Path(temporary) / "Probe.lean"
        source.write_text(PROBES, encoding="utf-8")
        result = subprocess.run([str(ROOT / "run-lake.sh"), "env", "lean", str(source)],
                                cwd=ROOT, capture_output=True, text=True)
        (logdir / "probes.log").write_text(result.stdout + result.stderr, encoding="utf-8")
        if result.returncode:
            raise ValueError("Lean probes failed; see .lake/statement-audit/probes.log")
    found = {}
    pattern = r"'([^']+)' depends on axioms: \[([^\]]*)\]"
    for name, axioms in re.findall(pattern, result.stdout):
        found[name] = {item.strip() for item in axioms.split(",") if item.strip()}
    for target in TARGETS:
        if target not in found or not found[target] <= PERMITTED:
            raise ValueError("Missing or unauthorized axiom report: " + target)
    bridges = (
        "QuantumChannelContinuity.referenceFirstOutput_swap",
        "QuantumChannelContinuity.channelRenyi_eq_referenceFirst",
        "QuantumChannelContinuity.channelRelative_eq_referenceFirst",
    )
    for name in bridges:
        if name not in found or not found[name] <= PERMITTED:
            raise ValueError("Missing or unauthorized bridge axiom report: " + name)
    after, _ = verify_current_identity()
    after_hashes = {record["path"]: record["sha256"] for record in after["files"]}
    after_hashes.update({record["path"]: record["sha256"] for record in after["checker_inputs"]})
    if after_hashes != before:
        raise ValueError("Current proof or checker sources changed during mechanical checking")
    after_dependencies = dependency_inputs(report)
    if after_dependencies != dependencies:
        raise ValueError("Live dependency inputs changed during mechanical checking")
    evidence = {
        "status": "passed",
        "probe_sha256": sha256(PROBES.encode("utf-8")),
        "probe_output_sha256": sha256((result.stdout + result.stderr).encode("utf-8")),
        "target_axioms": {name: sorted(found[name]) for name in TARGETS},
        "bridge_axioms": {name: sorted(found[name]) for name in bridges},
        "scope": "exact-type, defining-equation, normalization, domain and axiom probes",
        "semantic_correspondence_automated": False,
        "temporary_lean_source_removed": True,
        "source_sha256": before,
        "sources_unchanged": True,
        "dependency_source_sha256": dependencies["source_sha256"],
        "dependency_package_revisions": dependencies["package_revisions"],
        "dependency_inputs_unchanged": True,
        "historical_assessment_sha256": sha256(report_path.read_bytes()),
        "historical_input_scope": "retained pre-cleanup snapshot; not a new semantic assessment of current proof bytes",
    }
    (logdir / "result.json").write_text(json.dumps(evidence, indent=2) + "\n", encoding="utf-8")
    print("STATEMENT AUDIT MECHANICAL CHECK PASSED")
    print("Fresh probes check current types, equations, domains and axioms; the retained semantic assessment remains historical.")
    print("Paper correspondence still requires reading the source and definitions.")
    print("Fresh evidence: .lake/statement-audit/result.json")


if __name__ == "__main__":
    try:
        run()
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        try:
            logdir = ROOT / ".lake" / "statement-audit"
            logdir.mkdir(parents=True, exist_ok=True)
            (logdir / "result.json").write_text(json.dumps({
                "status": "failed", "error": str(error),
                "semantic_correspondence_automated": False,
            }, indent=2) + "\n", encoding="utf-8")
        except OSError:
            pass  # Preserve the nonzero exit if failure evidence cannot be saved.
        print("STATEMENT AUDIT CHECK FAILED: " + str(error), file=sys.stderr)
        sys.exit(1)
