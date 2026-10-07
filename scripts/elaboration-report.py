#!/usr/bin/env python3
# Copyright (c) 2026 Jinzhao Wang. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Jinzhao Wang (AI-assisted formalization)

"""Render evidence-bound elaboration reports; never build or edit Lean sources.

Example: python3 scripts/elaboration-report.py --label after --prior before \
    --date 2026-10-06 --findings docs/elaboration/interventions.json --publish-inputs
"""

import argparse
from collections import Counter
from datetime import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess

ROOT = Path(__file__).resolve().parent.parent
SKILL_PIN = "70bb859295edc2abb9ad81f8f6e31ab2adf8ca07"
SKILL_BASE = "https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/" + SKILL_PIN
EXPECTED_PROFILE_FILES = (
    "QuantumChannelContinuity/SDPCone.lean",
    "QuantumChannelContinuity/Schatten.lean",
    "QuantumChannelContinuity/TensorChannels.lean",
    "QuantumChannelContinuity/FilterAlignment.lean",
    "QuantumChannelContinuity/SDPTrace.lean",
    "QuantumChannelContinuity/SourceCorrespondence.lean",
    "QuantumChannelContinuity/Filter.lean",
    "QuantumChannelContinuity/OrderConvexity.lean",
    "QuantumChannelContinuity/RegularizationSup.lean",
)
ENV = os.environ.copy()
if os.name == "posix" and Path("/Library/Developer/CommandLineTools").exists():
    ENV["DEVELOPER_DIR"] = "/Library/Developer/CommandLineTools"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_json(file):
    return json.loads(file.read_text())


def git_blob(commit, file):
    return subprocess.check_output(["git", "show", commit + ":" + file], cwd=ROOT, env=ENV)


def resolved(file):
    return file if file.is_absolute() else ROOT / file


def clean_string(value):
    """Published commands use a checkout placeholder; external home paths vanish."""
    value = str(value).replace(str(ROOT), "<checkout>")
    return re.sub(r"/(?:Users|home)/[^\s\"']+", "<external-path>", value)


def process_records(values):
    records = []
    for value in values:
        if isinstance(value, dict):
            records.append(value)
            continue
        fields = str(value).strip().split(None, 2)
        records.append({"pid": fields[0] if fields else "unavailable",
                        "elapsed": fields[1] if len(fields) > 1 else "unavailable",
                        "kind": "checkout command" if str(ROOT) in str(value) else
                                "external or relative command; full command omitted"})
    return records


def sanitized(value, key=""):
    if key.startswith("process_inventory_"):
        return process_records(value)
    if isinstance(value, dict):
        return {k: sanitized(v, k) for k, v in value.items()}
    if isinstance(value, list):
        return [sanitized(v, key) for v in value]
    return clean_string(value) if isinstance(value, str) else value


def fmt(value, places=2):
    return "—" if value is None else f"{float(value):,.{places}f}"


def delta(value, before, places=2):
    if value is None or before is None:
        return "—"
    return f"{float(value) - float(before):+,.{places}f}"


def percent(value, before):
    if value is None or before in (None, 0):
        return "—"
    return f"{100 * (float(value) / float(before) - 1):+.1f}%"


def cell(value):
    return clean_string(value).replace("|", "\\|").replace("\n", " ")


def table(headers, rows):
    lines = ["| " + " | ".join(headers) + " |", "| " + " | ".join("---" for _ in headers) + " |"]
    lines.extend("| " + " | ".join(cell(c) for c in row) + " |" for row in rows)
    return "\n".join(lines)


def cpu(metrics):
    timing = metrics.get("timing", {})
    user, system = timing.get("User time (seconds)"), timing.get("System time (seconds)")
    return None if user is None or system is None else user + system


def module_times(metrics):
    result = {}
    for item in metrics.get("file_times", []):
        name = item["module"].split(":", 1)[0]
        result[name] = result.get(name, 0) + item["seconds"]
    return result


def committed_analysis(metrics):
    """Bind import edges and source diagnostics to measured Git bytes, not HEAD."""
    sources, mismatches = {}, []
    for file, digest in metrics.get("source_sha256", {}).items():
        data = git_blob(metrics["commit"], file)
        if sha(data) != digest:
            mismatches.append(file)
        if file.endswith(".lean"):
            sources[file] = data.decode()
    if mismatches:
        raise ValueError("Measured commit/source SHA mismatch: " + ", ".join(mismatches))
    costs = module_times(metrics)
    files = {file.removesuffix(".lean").replace("/", "."): file for file in sources}
    graph = {}
    for name, file in files.items():
        imports = []
        for line in sources[file].splitlines():
            match = re.match(r"^(?:(?:public|private)\s+)?(?:meta\s+)?import\s+(.+)", line)
            if match:
                imports.extend(match.group(1).split("--", 1)[0].split())
        graph[name] = [dep for dep in imports if dep in files]
    memo, visiting = {}, set()

    def longest(name):
        if name in memo:
            return memo[name]
        if name in visiting:
            raise ValueError("Cycle in committed project import graph: " + name)
        visiting.add(name)
        value, chain = max((longest(dep) for dep in graph.get(name, [])), default=(0, []), key=lambda x: x[0])
        memo[name] = (value + costs.get(name, 0), chain + [name])
        visiting.remove(name)
        return memo[name]

    critical, chain = max((longest(name) for name in costs), default=(0, []), key=lambda x: x[0])
    overrides = []
    for file, text in sources.items():
        for line_number, line in enumerate(text.splitlines(), 1):
            hit = re.match(r"\s*set_option\s+(maxHeartbeats|synthInstance.maxHeartbeats|maxRecDepth)\s+(\S+)", line)
            if hit:
                overrides.append({"file": file, "line": line_number, "option": hit.group(1), "value": hit.group(2)})
    return {"critical_path_seconds": critical, "critical_path": chain,
            "module_files": files, "timing_modules_found_in_git": sum(name in files for name in costs),
            "override_counts": dict(Counter(x["option"] + "=" + x["value"] for x in overrides)),
            "overrides": overrides, "largest_files": sorted(
                ({"file": f, "lines": len(t.splitlines())} for f, t in sources.items()),
                key=lambda x: -x["lines"])[:5]}


def evidence_bytes(file, expected_sha):
    """Accept raw local evidence or a hash-bound documented privacy projection."""
    data = file.read_bytes()
    if sha(data) == expected_sha:
        return data
    publication_file = file.parent / "publication.json"
    if publication_file.exists():
        publication = read_json(publication_file)
        original = publication.get("original_inputs_sha256", {}).get(file.name)
        published = publication.get("published_sha256", {}).get(file.name)
        if original == expected_sha and published == sha(data):
            return data
    raise ValueError("Evidence SHA mismatch: " + str(file))


def verify_parser_correction(metrics, metrics_file):
    correction = metrics.get("analysis_correction")
    if correction is None:
        return None
    if correction.get("kind") != "intentional-sorry-warning-quote-parser":
        raise ValueError("Unsupported retrospective analysis correction")
    original_file = metrics_file.parent / "metrics-original-parser.json"
    correction_file = metrics_file.parent / "parser-correction.json"
    log_file = metrics_file.parent / "build.txt"
    original = json.loads(evidence_bytes(original_file, correction["original_metrics_sha256"]))
    if read_json(correction_file) != correction:
        raise ValueError("Parser-correction sidecar differs from metric metadata")
    log = evidence_bytes(log_file, correction["raw_build_log_sha256"]).decode()
    expected_reasons = {
        "Missing intentional reference/control warning: ComparatorChallenges/ChannelRenyiContinuity.lean",
        "Missing intentional reference/control warning: ComparatorChallenges/MissingProof.lean",
    }
    if (original.get("valid") is not False or original.get("exit_code") != 0 or
            set(original.get("invalid_reasons", [])) != expected_reasons or
            original.get("dependency_artifacts_unchanged") is not True):
        raise ValueError("Correction is not restricted to the known warning-parser false invalidation")
    if metrics.get("original_valid") is not False or metrics.get("original_invalid_reasons") != original["invalid_reasons"]:
        raise ValueError("Original false-invalid result was not preserved")
    mutable_census_fields = {"valid", "invalid_reasons", "sorry_warnings", "sorry_census"}
    for key, value in original.items():
        if key not in mutable_census_fields and metrics.get(key) != value:
            raise ValueError("Retrospective correction changed execution evidence: " + key)
    execution_sha = correction["execution_script_sha256"]
    analysis_sha = correction["corrected_script_sha256"]
    if (original.get("measurement_script_sha256") != execution_sha or
            metrics.get("measurement_script_sha256") != execution_sha or
            metrics.get("analysis_script_sha256") != analysis_sha):
        raise ValueError("Execution and analysis script SHA roles were not preserved")
    script = git_blob(metrics["commit"], "scripts/elaboration-test.py")
    old_line = b'    sorries = [line for line in warnings if "uses \'sorry\'" in line]\n'
    new_line = b'    sorries = [line for line in warnings if re.search(r"declaration uses [`\']sorry[`\']", line)]\n'
    if sha(script) != execution_sha or script.count(old_line) != 1 or sha(script.replace(old_line, new_line, 1)) != analysis_sha:
        raise ValueError("Corrected analysis script is not exactly the documented one-line parser replacement")
    warnings = [line for line in log.splitlines() if line.startswith("warning:")]
    sorries = [line for line in warnings if re.search(r"declaration uses [`']sorry[`']", line)]
    census = dict(Counter(line.split(":", 2)[1].strip() for line in sorries))
    expected_census = {"ComparatorChallenges/ChannelRenyiContinuity.lean": 3,
                       "ComparatorChallenges/MissingProof.lean": 1}
    if (census != expected_census or metrics.get("sorry_census") != census or
            metrics.get("sorry_warnings") != len(sorries) or
            metrics.get("valid") is not True or metrics.get("invalid_reasons") != []):
        raise ValueError("Corrected validity/census does not follow the unchanged raw log")
    return {"verified": True, "kind": correction["kind"], "execution_script_sha256": execution_sha,
            "analysis_script_sha256": analysis_sha, "raw_build_log_sha256": correction["raw_build_log_sha256"],
            "original_metrics_sha256": correction["original_metrics_sha256"],
            "timing_reexecuted": False, "only_execution_source_difference": "one warning-parser line"}


def load_snapshot(label, metrics_file=None, profiles_file=None):
    metrics_file = resolved(Path(metrics_file or f".lake/elaboration/{label}/metrics.json"))
    profiles_file = resolved(Path(profiles_file or metrics_file.parent / "profiles.json"))
    metrics = read_json(metrics_file)
    if not re.fullmatch(r"[0-9a-f]{40}", metrics.get("commit", "")):
        raise ValueError("Measurement commit must be a full Git SHA")
    correction = verify_parser_correction(metrics, metrics_file)
    profiles_available = profiles_file.exists()
    profiles = read_json(profiles_file) if profiles_available else {"profiles": [], "sources_unchanged": None}
    source_hashes = metrics.get("source_sha256", {})
    profile_binding_errors = []
    profile_start = profiles.get("started_sources")
    profile_start = profile_start if isinstance(profile_start, dict) else {}
    if profiles_available:
        # The profiled declaration can remain byte-identical while an imported
        # source or pin changes. Bind the complete inventory, not only the leaf.
        if profiles.get("started_sources") != source_hashes:
            profile_binding_errors.append("complete profile started_sources inventory differs from measured source/pin inventory")
        if profiles.get("sources_unchanged") is not True:
            profile_binding_errors.append("profile source inventory was not verified unchanged")
    for profile in profiles.get("profiles", []):
        if profile["file"] not in source_hashes or not re.fullmatch(r"[0-9a-f]{64}", profile.get("source_sha256", "")):
            profile_binding_errors.append(profile["file"] + ": missing owned source or valid SHA256 binding")
        if profile.get("source_sha256") != source_hashes.get(profile["file"]):
            profile_binding_errors.append(profile["file"] + ": leaf source SHA differs from measured inventory")
        if profile.get("source_sha256") != profile_start.get(profile["file"]):
            profile_binding_errors.append(profile["file"] + ": leaf source SHA differs from profile start inventory")
        if profile.get("exit_code") != 0:
            profile_binding_errors.append(profile["file"] + ": warm profile did not exit successfully")
        if profile.get("dependency_artifacts_unchanged") is not True:
            profile_binding_errors.append(profile["file"] + ": dependency artifact preservation was not verified")
    if profile_binding_errors:
        raise ValueError("Invalid warm-profile evidence: " + "; ".join(profile_binding_errors))
    observed_files = [profile["file"] for profile in profiles.get("profiles", [])]
    observed_set = set(observed_files)
    expected_set = set(EXPECTED_PROFILE_FILES)
    missing = sorted(expected_set - observed_set)
    unexpected = sorted(observed_set - expected_set)
    duplicates = sorted(name for name, count in Counter(observed_files).items() if count > 1)
    complete = profiles_available and not missing and not unexpected and not duplicates
    return {"label": label, "metrics": metrics, "profiles": profiles,
            "metrics_path": metrics_file, "profiles_path": profiles_file,
            "metrics_sha256": sha(metrics_file.read_bytes()),
            "profiles_sha256": sha(profiles_file.read_bytes()) if profiles_file.exists() else None,
            "profile_binding_errors": profile_binding_errors,
            "profiles_validated": complete,
            "profile_selection": {"expected_files": list(EXPECTED_PROFILE_FILES),
                                  "completed_files": observed_files, "missing_files": missing,
                                  "unexpected_files": unexpected, "duplicate_files": duplicates,
                                  "complete": complete},
            "parser_correction_verified": correction,
            "analysis": committed_analysis(metrics)}


def phase(profile, category):
    values = profile.get("cumulative_phases_seconds", {})
    normalized = {re.sub(r"[ _-]", "", k.lower()): v for k, v in values.items()}
    aliases = {"import": ["import"], "typeclass": ["typeclassinference", "typeclasssynthesis"],
               "simp": ["simp", "simplification"], "elaboration": ["elaboration"],
               "typechecking": ["typechecking", "typecheck"], "tactic": ["tacticexecution"]}
    for candidate in aliases[category]:
        if candidate in normalized:
            return normalized[candidate]
    return None


def top_five_selection(snapshot, supplemental=None):
    top = sorted(module_times(snapshot["metrics"]).items(), key=lambda item: -item[1])[:5]
    files = snapshot["analysis"]["module_files"]
    planned = [files[name] for name, _ in top if name in files]
    observed = {item["file"] for item in snapshot["profiles"].get("profiles", [])}
    if supplemental:
        observed.update(item["file"] for item in supplemental["profiles"].get("profiles", []))
    return {"top_five_modules": [name for name, _ in top], "top_five_files": planned,
            "unmapped_modules": [name for name, _ in top if name not in files],
            "expected_supplemental_files": [file for file in planned if file not in EXPECTED_PROFILE_FILES],
            "missing_files": [file for file in planned if file not in observed],
            "complete": not any(name not in files for name, _ in top) and all(file in observed for file in planned)
                and (supplemental is None or supplemental["supplemental_selection"]["complete"])}


def load_supplemental(snapshot, profiles_file):
    # Reuse the exact whole-inventory/leaf/exit/artifact validation of the paired
    # set. This is a separate diagnostic selection, never a tenth paired file.
    if not resolved(Path(profiles_file)).exists():
        raise FileNotFoundError("Supplemental profiles input does not exist: " + str(profiles_file))
    extra = load_snapshot(snapshot["label"] + "-top-five", snapshot["metrics_path"], profiles_file)
    expected = top_five_selection(snapshot)["expected_supplemental_files"]
    observed = [item["file"] for item in extra["profiles"].get("profiles", [])]
    missing = sorted(set(expected) - set(observed))
    unexpected = sorted(set(observed) - set(expected))
    duplicates = sorted(file for file, count in Counter(observed).items() if count > 1)
    extra["supplemental_selection"] = {"expected_files": expected, "completed_files": observed,
        "missing_files": missing, "unexpected_files": unexpected, "duplicate_files": duplicates,
        "complete": not missing and not unexpected and not duplicates}
    extra["profiles_validated"] = False
    return extra


def supplemental_text(snapshot, extra, output, report_date):
    selection = extra["supplemental_selection"]
    parts = ["<!-- Copyright (c) 2026 Jinzhao Wang. Released under Apache 2.0; see LICENSE. -->",
        f"# Supplemental current top-five profiles — {report_date}",
        "Measured source commit: `" + snapshot["metrics"]["commit"] + "`. Main metrics input SHA256: `" +
        snapshot["metrics_sha256"] + "`; supplemental profiles input SHA256: `" + extra["profiles_sha256"] + "`.",
        "These are **unpaired diagnostic profiles** of actual current top-five modules outside the frozen nine-file set. They do not add a cold build, replace the paired set, change its comparison gate, or establish a before/after speedup. Whole source/pin inventories, leaf hashes, successful exits and unchanged dependency artifacts have the same guards as the paired profiles.",
        "Supplemental selection complete: **" + str(selection["complete"]) + "**. Expected: " + cell(selection["expected_files"]) +
        "; missing: " + cell(selection["missing_files"]) + "; unexpected: " + cell(selection["unexpected_files"]) +
        "; duplicates: " + cell(selection["duplicate_files"]) + "."]
    if not selection["complete"]:
        parts.append("This is a provisional successful prefix, not complete supplemental coverage.")
    rows = extra["profiles"].get("profiles", [])
    parts.append(table(["File", "Warm wall (s)", "Import", "Typeclass", "Simp", "Elaboration", "Type checking", "Tactic execution"],
        [("`" + item["file"] + "`", fmt(item.get("timing", {}).get("wall_seconds")),
          *(fmt(phase(item, key)) for key in ("import", "typeclass", "simp", "elaboration", "typechecking", "tactic"))) for item in rows]))
    parts.append("Flat counters aggregate elapsed durations across Lean threads/tasks and can exceed wall time. They do not partition wall time or measure process CPU. Phase routing ratios are heuristics, and missing labels are not zeroes.")
    for item in rows:
        parts.append("**`" + item["file"] + "`**: " + classified(item) + ". Source SHA256: `" + item["source_sha256"] +
            "`; raw log SHA256: `" + item.get("log_sha256", "unavailable") + "`. All reported phases: `" +
            json.dumps(item.get("cumulative_phases_seconds", {}), sort_keys=True) + "`.")
    return "\n\n".join(parts) + "\n"


def classified(profile):
    wall = profile.get("timing", {}).get("wall_seconds")
    if not wall:
        return "Unclassified: warm wall timing unavailable"
    values = profile.get("cumulative_phases_seconds", {})
    candidates = sorted(((k, v) for k, v in values.items() if v > 5 and v > 0.25 * wall),
                        key=lambda item: -item[1])
    if not candidates:
        return "No component counter exceeds the >5s and >25%-of-warm-wall screening thresholds"

    def route(name):
        normalized = re.sub(r"[ _-]", "", name.lower())
        if normalized == "import":
            return "consumer import narrowing candidate; no local-proof cause inferred"
        if normalized in ("typeclassinference", "typeclasssynthesis"):
            return "typeclass trace needed to distinguish named expensive searches from a diffuse floor before proposing caches"
        if "interpretation" in normalized and "linarith" in normalized:
            return "explicit arithmetic inequalities candidate; confirm per-call attribution"
        if normalized in ("simp", "simplification"):
            return "narrow only measured expensive simp calls"
        if "elaboration" in normalized:
            return "unattributed elaboration requires a per-declaration trace before assigning a cause"
        return "per-declaration or per-tactic attribution needed before selecting a cleanup lever"

    name, seconds = candidates[0]
    text = f"Largest qualified counter: `{name}` ({fmt(seconds)} s) — {route(name)}"
    if len(candidates) > 1:
        text += ". Other qualified counters: " + "; ".join(
            f"`{other}` ({fmt(value)} s) — {route(other)}" for other, value in candidates[1:])
    return text + ". These are routing screens, not a partition of wall-clock time"


def event_seconds(line):
    match = re.search(r"took\s+([\d.]+)(ms|s)", line)
    if not match:
        return None
    value, unit = match.groups()
    return float(value) / (1000 if unit == "ms" else 1)


def comparison_gate(current, prior):
    if not prior:
        return {"wall_comparable": False, "notes": ["This snapshot is the first clean baseline; no trend claim is made."]}
    a, b = current["metrics"], prior["metrics"]
    notes, comparable = [], True
    for key, description in (("time_tool", "GNU timing tool"), ("time_binary", "GNU timing binary"),
                             ("targets", "build targets"), ("lean", "Lean version"),
                             ("host", "host/platform"), ("cores", "logical core count"),
                             ("scheduling", "Lake scheduling"),
                             ("measurement_script_sha256", "measurement script"),
                             ("size_counter_sha256", "size counter")):
        if a.get(key) != b.get(key):
            if key == "measurement_script_sha256":
                ca, cb = current.get("parser_correction_verified"), prior.get("parser_correction_verified")
                a_analysis = ca["analysis_script_sha256"] if ca else a.get(key)
                b_analysis = cb["analysis_script_sha256"] if cb else b.get(key)
                if a_analysis == b_analysis and (ca or cb):
                    notes.append("Execution script SHAs differ only by the independently checked one-line intentional-sorry warning parser correction. Original execution SHA/timing and false-invalid baseline result are preserved; the saved raw log was reclassified without retiming. This is a documented analysis correction, not silently identical instrumentation.")
                    continue
            notes.append("Unmatched " + description + "; wall-clock trend is not comparable.")
            comparable = False
    for file in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        if a.get("source_sha256", {}).get(file) != b.get("source_sha256", {}).get(file):
            notes.append("Changed pin/configuration " + file + "; comparison is not isolated to source cleanup.")
            comparable = False
    if any(not metric.get("host") or not metric.get("cores") for metric in (a, b)):
        notes.append("Host/core metadata is incomplete; hardware comparability is not established.")
        comparable = False
    pa, pb = a.get("implied_parallelism"), b.get("implied_parallelism")
    matched = pa is not None and pb is not None and max(pa, pb) > 0 and abs(pa - pb) / max(pa, pb) <= 0.10
    if not matched:
        notes.append("Logged implied parallelism differs by more than the report's 10% descriptive tolerance; no wall-speedup claim.")
        comparable = False
    ca, cb = cpu(a), cpu(b)
    sa, sb = a.get("logged_module_elapsed_sum_seconds"), b.get("logged_module_elapsed_sum_seconds")
    flags = []
    if ca is not None and cb is not None and sa is not None and sb is not None and ca < cb and sa > sb:
        flags.append("measured CPU down while logged module elapsed sum rose")
    if pa is not None and pb not in (None, 0) and pa > pb * 1.10:
        flags.append("logged implied parallelism rose by more than 10%")
    ta, tb = module_times(a), module_times(b)
    positive = sum(ta[n] > tb[n] * 1.10 for n in ta.keys() & tb.keys())
    negative = sum(ta[n] < tb[n] * 0.90 for n in ta.keys() & tb.keys())
    if positive >= 2 and negative >= 2:
        flags.append("same-file logged times moved both up and down by more than 10%")
    if len(flags) >= 2:
        notes.append("At least two contention indicators are present: " + "; ".join(flags) + ". Treat the run pair as contention-bound; skip structural conclusions from build durations.")
        comparable = False
    else:
        notes.append("Contention indicators detected: " + ("; ".join(flags) if flags else "none under the stated descriptive thresholds") + ".")
    if any(process_records(m.get("process_inventory_before", [])) or process_records(m.get("process_inventory_after", [])) for m in (a, b)):
        notes.append("Co-running Lean/Lake commands were observed. Presence alone neither invalidates the run nor proves contamination; actual source/dependency mutation guards determine validity.")
    if not a.get("valid") or not b.get("valid"):
        comparable = False
        notes.append("At least one measurement is invalid; do not infer a performance improvement.")
    if not current.get("profiles_validated") or not prior.get("profiles_validated"):
        comparable = False
        notes.append("At least one complete warm-profile set is missing. This is a preliminary diagnostic only; no performance-improvement conclusion is authorized.")
    if comparable:
        notes.append("Same timing tool, pins, targets and scheduler; implied parallelism is within 10%. Wall results are descriptively comparable, but one rebuild per state does not establish a statistically robust speedup.")
    return {"wall_comparable": comparable, "matched_implied_parallelism": matched,
            "parallelism_tolerance": 0.10, "contention_indicators": flags, "notes": notes}


def findings_text(data):
    if not data:
        return "No intervention record was supplied. These profiles establish measurements and candidates; they do not claim an applied or successful optimization."
    entries = data if isinstance(data, list) else data.get("interventions", data.get("findings", []))
    if not isinstance(entries, list) or not entries:
        return "The supplied findings record contains no listed interventions."
    def phase_gain(entry):
        if entry.get("before_seconds") is not None and entry.get("after_seconds") is not None:
            return entry["before_seconds"] - entry["after_seconds"]
        if entry.get("before_typeclass_seconds") is not None and entry.get("after_typeclass_seconds") is not None:
            return entry["before_typeclass_seconds"] - entry["after_typeclass_seconds"]
        return 0

    def actionable_rank(item):
        index, entry = item
        retained = entry.get("status") == "retained"
        traced = entry.get("trace_diagnosis") or entry.get("trace_evidence")
        if retained and traced and entry.get("lever") != "consumer import narrowing":
            return (0, -phase_gain(entry), index)
        if retained and entry.get("lever") == "consumer import narrowing":
            return (1, -phase_gain(entry), index)
        if retained:
            return (2, -phase_gain(entry), index)
        rejected = entry.get("status") in ("reverted", "rejected", "failed")
        return (4 if rejected else 3, 0, index)

    entries = [entry for _, entry in sorted(enumerate(entries), key=actionable_rank)]
    chunks = ["Ranked by actionability: retained trace-supported closed-head caches first, retained import reductions next by measured phase decrease, other candidates next, rejected probes last. The retained import order uses **one A/B sample per state**, not a statistical ranking of stable speedups. A named trace mechanism supports the cache diagnosis without attributing whole-build changes to it."]
    for index, entry in enumerate(entries, 1):
        title = entry.get("description", entry.get("title", entry.get("id", f"Finding {index}")))
        chunks.append(f"{index}. **{cell(title)}** — lever: {cell(entry.get('lever', 'not specified'))}; status: {cell(entry.get('status', 'not specified'))}.")
        detail = {k: v for k, v in entry.items() if k not in ("description", "title", "id", "lever", "status")}
        if detail:
            chunks.append("\n```json\n" + json.dumps(sanitized(detail), ensure_ascii=False, indent=2) + "\n```")
        if entry.get("id") == "hermitian-module" and entry.get("evidence_before") and entry.get("evidence_after"):
            samples = []
            for key, source_key in (("evidence_before", "baseline_source_sha256"), ("evidence_after", "variant_source_sha256")):
                evidence = read_json(resolved(Path(entry[key])))
                if evidence.get("sources_unchanged") is not True or len(evidence.get("profiles", [])) != 1:
                    raise ValueError("Invalid cache A/B evidence for memory disclosure")
                sample = evidence["profiles"][0]
                if sample.get("file") != entry.get("file") or sample.get("source_sha256") != entry.get(source_key) or \
                        sample.get("source_sha256") != evidence.get("started_sources", {}).get(entry.get("file")) or \
                        sample.get("exit_code") != 0 or sample.get("dependency_artifacts_unchanged") is not True:
                    raise ValueError("Invalid cache A/B leaf/exit/artifact evidence for memory disclosure")
                samples.append(sample.get("timing", {}).get("Maximum resident set size (kbytes)"))
            if all(value is not None for value in samples):
                before_rss, after_rss = samples
                chunks.append("The provider's warm A/B peak accounted RSS rose from **" + fmt(before_rss, 0) + " to " +
                    fmt(after_rss, 0) + " KiB** (" + percent(after_rss, before_rss) + "). This is a memory observation from one pair; the phase screen does not establish a stable global memory improvement or attribute this rise to the cache alone.")
    return "\n\n".join(chunks)


def relative_link(target, output):
    return os.path.relpath(target, output.parent).replace(os.sep, "/")


def report(snapshot, prior, findings, output, report_date, supplemental=None):
    m, p, analysis = snapshot["metrics"], snapshot["profiles"], snapshot["analysis"]
    old = prior["metrics"] if prior else {}
    timing, old_timing = m.get("timing", {}), old.get("timing", {})
    gate = comparison_gate(snapshot, prior)
    sections = ["<!-- Copyright (c) 2026 Jinzhao Wang. Released under Apache 2.0; see LICENSE. -->",
                f"# Elaboration report — {report_date} — {snapshot['label'].upper()}",
                "## 1. Setup and provenance",
                f"Measured commit: `{m['commit']}`. UTC window: `{m.get('started_utc', 'unavailable')}` to `{m.get('finished_utc', 'unavailable')}`. Host: `{cell(m.get('host', 'unavailable'))}`; reported logical cores: {m.get('cores', 'unavailable')}. Lean: `{cell(m.get('lean', 'unavailable'))}`.",
                f"The report/filename date `{report_date}` labels the cleanup campaign, not necessarily this run's UTC date. The recorded measurement UTC timestamps are authoritative.",
                f"Timing tool: `{cell(m.get('time_tool', 'unavailable'))}` using `-v`. Scheduling: {cell(m.get('scheduling', 'unavailable'))}. Explicit targets: `{', '.join(m.get('targets', []))}`. These targets cover the committed facade import closure plus Comparator specifications/controls. Lake's default library globs select root modules, not every submodule. The timed scope is 83 owned modules; the supplementary `SourceCorrespondence` module is outside that cold-build closure.",
                "Only the checkout's resolved `.lake/build` was invalidated after rejecting symlinks or dependency caches nested in that subtree. Dependencies remained inputs. No `lake clean` or `lake update` is part of this measurement.",
                f"Observed Lean/Lake process entries before/after: {len(m.get('process_inventory_before', []))}/{len(m.get('process_inventory_after', []))}. Full external commands are omitted to avoid publishing unrelated checkout paths. These regex-filtered snapshots are an incomplete inventory, not continuous monitoring of load or other wrappers. Process presence is informational; it did not gate the test.",
                f"Metrics input SHA256: `{snapshot['metrics_sha256']}`. Profiles input SHA256: `{snapshot['profiles_sha256'] or 'not available'}`. Every source/pin SHA was checked against the measured Git commit; the complete warm-profile starting inventory and each leaf source are bound to that same inventory. Warm-profile source-binding mismatches: {len(snapshot['profile_binding_errors'])}. Complete warm-profile set validated: {snapshot.get('profiles_validated', False)}.",
                f"Size counter pin: `{m.get('size_counter_commit', 'unavailable')}`; counter SHA256: `{m.get('size_counter_sha256', 'unavailable')}`; measurement-script SHA256: `{m.get('measurement_script_sha256', 'unavailable')}`.",
                "## 2. Size snapshot"]
    correction = snapshot.get("parser_correction_verified")
    if correction:
        sections.insert(-1, "**Documented warning-parser correction:** this build initially exited successfully but was falsely marked invalid because the parser expected single-quoted `sorry` while Lean emitted backticks. The original false-invalid metrics and setup remain preserved. Reclassification counted the four authorized warnings in the unchanged SHA-bound raw log; timing, commands, sources and dependency evidence were not changed or rerun. Original execution script SHA256: `" + correction["execution_script_sha256"] + "`; corrected analysis script SHA256: `" + correction["analysis_script_sha256"] + "`. The renderer independently verified the exact one-line source replacement and the original/corrected census.")
    sections.append(table(["Git-tree measure", "This snapshot", "Prior", "Δ"],
                          [(key, value, old.get("size", {}).get(key, "—"), delta(value, old.get("size", {}).get(key), 0))
                           for key, value in m.get("size", {}).items()]))
    nonmodule = m.get("size", {}).get("non-module files")
    sections.append(f"The pinned counter reported **{nonmodule if nonmodule is not None else 'an unavailable count of'} non-module files**. This project uses the legacy import-file convention. The skill's zero-non-module structural criterion is **not met**; a module-system migration is outside this performance cleanup. The report is not an unqualified claim that every skill criterion passed.")
    sections.append("The committed tree has 84 mathematical/library modules including the three Comparator challenge/control modules, plus five explicitly run scripts/audits. The timed facade closure builds 83 owned modules: `QuantumChannelContinuity.SourceCorrespondence` is the one supplemental mathematical module outside that closure. It is profiled directly in both serial profile sets as a supplemental measurement, rather than silently included in cold-build totals. The final `check.sh` explicitly builds it and the root audit imports it. Thus tree file count, timed module count and final full-check scope differ deliberately. Comment-only exclusions follow the unmodified pinned counter. The first timed snapshot was taken **after** the dead-code sweep, so this pair does not measure the sweep's performance benefit.")
    sections.append("## 3. Headline table")
    rows = []
    fields = [("Wall (s)", timing.get("wall_seconds"), old_timing.get("wall_seconds")),
              ("User CPU (s)", timing.get("User time (seconds)"), old_timing.get("User time (seconds)")),
              ("System CPU (s)", timing.get("System time (seconds)"), old_timing.get("System time (seconds)")),
              ("Measured user + system CPU (s)", cpu(m), cpu(old)),
              ("GNU time %CPU", timing.get("Percent of CPU this job got"), old_timing.get("Percent of CPU this job got")),
              ("Peak RSS (reported KiB)", timing.get("Maximum resident set size (kbytes)"), old_timing.get("Maximum resident set size (kbytes)")),
              ("Peak RSS (GiB)", timing.get("Maximum resident set size (kbytes)", 0) / 1048576 if "Maximum resident set size (kbytes)" in timing else None,
               old_timing.get("Maximum resident set size (kbytes)", 0) / 1048576 if "Maximum resident set size (kbytes)" in old_timing else None),
              ("Lake total jobs, including cached dependencies", m.get("jobs"), old.get("jobs")),
              ("Compiled own modules", m.get("compiled_own_modules"), old.get("compiled_own_modules")),
              ("Summed Built elapsed durations (s; NOT CPU)", m.get("logged_module_elapsed_sum_seconds"), old.get("logged_module_elapsed_sum_seconds")),
              ("Logged implied parallelism (sum / wall)", m.get("implied_parallelism"), old.get("implied_parallelism")),
              ("Logged elapsed ms / non-comment line", m.get("logged_elapsed_ms_per_code_line"), old.get("logged_elapsed_ms_per_code_line"))]
    for name, value, before in fields:
        rows.append((name, fmt(value), fmt(before), delta(value, before), percent(value, before)))
    sections.append(table(["Metric", "This snapshot", "Prior", "Δ", "Relative Δ"], rows))
    sections.append(" ".join(gate["notes"]))
    seconds, cores = cpu(m), m.get("cores")
    sections.append(f"CPU/cores work-floor heuristic: **{fmt(seconds / cores if seconds is not None and cores else None)} s**. Longest weighted owned import chain: **{fmt(analysis['critical_path_seconds'])} s**, covering {analysis['timing_modules_found_in_git']}/{len(module_times(m))} logged modules with committed source paths. These are heuristic diagnostics, not a scheduler prediction or achievable wall-time guarantee.")
    sections.append("Weighted chain, imports first: " + " → ".join("`" + name + "`" for name in analysis["critical_path"]) + ".")
    sections.append("## 4. Build health")
    sections.append(table(["Check", "Result"], [("Measurement valid", m.get("valid")), ("Build exit", m.get("exit_code")),
        ("Errors", m.get("errors")), ("Warnings", m.get("warnings")), ("Intentional sorry warnings", m.get("sorry_warnings")),
        ("Dependency artifacts unchanged", m.get("dependency_artifacts_unchanged")),
        ("Profile source inventory unchanged", p.get("sources_unchanged")),
        ("Profile source bindings match measured commit", not snapshot["profile_binding_errors"])]))
    sections.append("The authorized warning census is exactly three missing bodies in `ComparatorChallenges/ChannelRenyiContinuity.lean` (reference specifications) and one in `ComparatorChallenges/MissingProof.lean` (negative control). These four warnings are not holes in the proof library. Any additional or missing warning invalidates the measurement guard.")
    sections.append("Observed sorry census: `" + json.dumps(m.get("sorry_census", {}), sort_keys=True) + "`.")
    if m.get("invalid_reasons"):
        sections.append("Invalidation reasons: " + "; ".join(map(cell, m["invalid_reasons"])) + ".")
    kinds = sorted(m.get("warning_kinds", {}).items(), key=lambda x: -x[1])
    sections.append(table(["Warning kind", "Count"], kinds[:12]) if kinds else "No other warning kinds were recorded.")
    sections.append("Committed resource-limit overrides: `" + json.dumps(analysis["override_counts"], sort_keys=True) + "`. The renderer reports existing overrides; it does not increase limits. No repository file-size threshold is claimed. Largest source files: " + "; ".join(f"`{item['file']}` ({item['lines']} lines)" for item in analysis["largest_files"]) + ".")
    sections.append("## 5. Heavy tail")
    sections.append(table(["Logged module tier", "Count", "Prior", "Δ"],
        [("≥" + tier + " s", count, old.get("heavy_tail", {}).get(tier, "—"), delta(count, old.get("heavy_tail", {}).get(tier), 0))
         for tier, count in m.get("heavy_tail", {}).items()]))
    prior_times = module_times(old)
    top = sorted(module_times(m).items(), key=lambda x: -x[1])[:30]
    sections.append(table(["Rank", "Own module", "Built elapsed (s)", "Prior (s)", "Δ (s)"],
        [(index, "`" + name + "`", fmt(value), fmt(prior_times.get(name)), delta(value, prior_times.get(name)))
         for index, (name, value) in enumerate(top, 1)]))
    timed = len(m.get("file_times", []))
    compiled = m.get("compiled_own_modules")
    sections.append(f"Timing-visible extraction: {timed} logged Built entries; reported compiled-own count {compiled}. The current parser defines that count from the same entries, so equality is not an independent completeness audit. Millisecond and second entries are included. Cached Lake jobs have no own compile duration and are excluded; no independent count of omitted/unlogged compilation jobs is available.")
    sections.append("## 6. Per-namespace elapsed-duration aggregation")
    groups = m.get("namespaces_logged_elapsed", {})
    old_groups = old.get("namespaces_logged_elapsed", {})
    sections.append(table(["Namespace / facade", "Summed elapsed (s)", "Prior (s)", "Δ (s)"],
        [(name, fmt(groups.get(name)), fmt(old_groups.get(name)), delta(groups.get(name), old_groups.get(name)))
         for name in sorted(groups.keys() | old_groups.keys())]))
    sections.append("These are sums of logged module elapsed durations by first namespace component, **not per-namespace CPU measurements**. Each duration includes startup, import loading and build outputs under the observed load.")
    sections.append("## 7. Serial warm own-file profiles")
    selection = snapshot.get("profile_selection", {})
    sections.append("Campaign profile set: **nine specified paired files**, including supplemental `SourceCorrespondence`. Complete set: " + str(selection.get("complete", False)) + ". Expected files: " + ", ".join("`" + file + "`" for file in selection.get("expected_files", [])) + ".")
    top_five = top_five_selection(snapshot, supplemental)
    sections.append("Actual current top-five own modules from the cold-build log: " + cell(top_five["top_five_modules"]) +
        ". Warm-profile coverage complete: **" + str(top_five["complete"]) + "**. Missing files: " + cell(top_five["missing_files"]) +
        "; unmapped modules: " + cell(top_five["unmapped_modules"]) + ". Current top-five files outside the frozen nine require a separate serial supplemental label; they must not be appended to the paired profile set.")
    if not selection.get("complete"):
        sections.append("**Provisional profile prefix:** the profiling tool saves successful prefixes after each file. Missing files: " + cell(selection.get("missing_files", [])) + "; unexpected files: " + cell(selection.get("unexpected_files", [])) + "; duplicates: " + cell(selection.get("duplicate_files", [])) + ". Individual supplied profiles remain source-bound, but this is not a completed elaboration test and the performance-comparison gate stays closed.")
    profiles = p.get("profiles", [])
    sections.append(table(["File", "Warm wall (s)", "Import", "Typeclass", "Simp", "Elaboration", "Type checking", "Tactic execution"],
        [("`" + item["file"] + "`", fmt(item.get("timing", {}).get("wall_seconds")),
          *(fmt(phase(item, key)) for key in ("import", "typeclass", "simp", "elaboration", "typechecking", "tactic"))) for item in profiles])
        if profiles else "No warm profiles were supplied; no profile-based cause is established.")
    sections.append("Phase values are seconds from the flat `--profile` cumulative counters. The pinned Lean `Lean.Util.Profile` documentation calls these **exclusive component execution times**: exclusion applies within an instrumented execution stack. Counters aggregate Lean threads/tasks, whose durations can overlap in wall time, so categories do not partition the GNU wall clock and their wall-time percentages need not total 100%. Their sum is not GNU process CPU or wall time; uninstrumented runtime and rounding can also differ. Structured `trace.profiler` trees are a separate profiler with nested durations that may overlap as well. A dash means that a flat label was absent, not a measured zero. Build elapsed durations and warm serial wall times measure different scopes. `SourceCorrespondence`, when present, is an explicitly additional paired supplemental profile; it is not one of the 83 cold-build modules.")
    sections.append("Primary implementation references: [thread-local parent stack, exclusive subtraction and global category accumulation](https://github.com/leanprover/lean4/blob/v4.29.0-rc6/src/library/time_task.cpp), [steady-clock elapsed timer](https://github.com/leanprover/lean4/blob/v4.29.0-rc6/src/util/timeit.h), and [flat-profiler option documentation](https://github.com/leanprover/lean4/blob/v4.29.0-rc6/src/Lean/Util/Profile.lean). Routing selects the largest qualified counter and lists other qualified counters. The >25%-of-warm-wall screen is a heuristic applied to aggregated timers, not a measured share of a wall-time partition.")
    for item in profiles:
        sections.append(f"**`{item['file']}`**: {classified(item)}. Exit: {item.get('exit_code')}; dependency artifacts unchanged: {item.get('dependency_artifacts_unchanged')}. Source SHA256: `{item.get('source_sha256')}`; raw profile SHA256: `{item.get('log_sha256')}`.")
        phases = item.get("cumulative_phases_seconds", {})
        sections.append("All reported cumulative phases: `" + json.dumps(phases, sort_keys=True) + "`.")
        raw_events = item.get("events_over_100ms", [])
        events = [line for line in raw_events if (event_seconds(line) or 0) > 0.1]
        sections.append(f"Reported event lines strictly over 100ms: {len(events)} ({len(raw_events)} raw duration lines parsed). This is not necessarily a count of unique calls, and sub-100ms events are not comprehensively exposed by Lean.")
        if events:
            sections.append("```text\n" + "\n".join(clean_string(line) for line in events) + "\n```")
    sections.append("## 8. Findings ranked by actionability")
    if supplemental:
        sections.append("Separate supplemental current top-five selection complete: **" + str(supplemental["supplemental_selection"]["complete"]) +
            "**. Supplemental input SHA256: `" + supplemental["profiles_sha256"] + "`. These unpaired diagnostics do not change the nine-file comparison gate.")
    sections.append(findings_text(findings))
    if m["commit"] in ("03dde86daf40a3752c273a3017399539e5c7def9", "8765c21753175381a57b29fa9469b35675515b2c"):
        sections.append("The separately bound [explicit import-closure audit](" + relative_link(ROOT / "docs/elaboration/import-closure.json", output) +
            ") finds a smaller source import closure in each of the six retained leaves, while the timed default-target union remains **3,584 non-toolchain modules** before and after. Narrower leaf imports do not establish a smaller global union or a timing benefit by themselves; explicit Lean/Init/Std/Lake boundaries and implicit prelude edges are excluded as disclosed in that audit.")
    sections.append("Keep an intervention only with measured evidence in its relevant phase (the cleanup skill uses ≥2 s or ≥10%), without moving cost to a worse consumer. Import-bound measurements route to consumer import narrowing. Large unassigned elaboration requires a per-declaration trace; diffuse typeclass time does not by itself identify a cacheable class.")
    sections.append("## 9. What is not established")
    sections.append("This snapshot does not prove global optimality, a statistically stable speedup, or equal background load. The logged sum is not CPU, and implied parallelism is a diagnostic ratio. GNU time 1.10 on this Darwin host reports RSS in KiB (validated against the platform's byte-valued resource counter); GiB is KiB / 1,048,576. Its peak RSS is the maximum accounted process/child RSS, not the sum of concurrent workers' simultaneous memory. Flat profiler categories are exclusive within instrumented execution stacks; aggregation across parallel threads/tasks can exceed wall time. They are not a wall-time partition, and their counter sum is not process CPU/wall time. Structured nested trace durations may also overlap. The import-chain estimate excludes upstream compilation because dependency oleans are inputs, and its elapsed weights can include contention.")
    sections.append("Two snapshots cannot establish a monotonic regression across three reports. No Δlines × prior-ms/line calculation predicts measured CPU: the normalized metric uses elapsed-duration sums instead. Unprofiled modules and unattributed elaboration remain outside a causal claim. Other Lean processes alone do not establish artifact mutation or invalidity. The legacy module-header criterion remains unmet. Missing warm profiles make this a preliminary diagnostic; invalid inventories, unsuccessful profile exits or unpreserved artifacts are rejected before rendering.")
    if snapshot["profile_binding_errors"]:
        sections.append("Warm profiles do not bind to measured source bytes for: " + ", ".join(map(cell, snapshot["profile_binding_errors"])) + ". Do not treat them as profiles of this snapshot.")
    sections.append("## 10. Methodology and exact commands")
    sections.append("The recorded timed command was:\n\n```bash\n" + clean_string(shlex.join(m.get("command", []))) + "\n```")
    if profiles:
        sections.append("Recorded warm commands, executed sequentially:\n\n```bash\n" + "\n".join(clean_string(shlex.join(item["command"])) for item in profiles) + "\n```")
    sections.append("Replay from the recorded commit using the dependency preparation, pinned skill checkout and GNU-time instructions in [the elaboration guide](" + relative_link(ROOT / "docs/elaboration/README.md", output) + "). Choose a fresh label; the measurement script rejects an existing build-label directory. Profile after the build, never in parallel batches.")
    sections.append("## 11. Pointers")
    pointers = [("Elaboration test skill", SKILL_BASE + "/skills/lean-elaboration-test/SKILL.md"),
                ("Measured cleanup skill", SKILL_BASE + "/skills/lean-elaboration/SKILL.md"),
                ("Dead-code sweep, before this baseline", relative_link(ROOT / "docs/DEAD_CODE_SWEEP_2026-10-06.md", output)),
                ("Reproduction guide", relative_link(ROOT / "docs/elaboration/README.md", output)),
                ("Metrics evidence", relative_link(ROOT / f"docs/elaboration/{snapshot['label']}/metrics.json", output)),
                ("Warm profile evidence", relative_link(ROOT / f"docs/elaboration/{snapshot['label']}/profiles.json", output))]
    if prior:
        pointers.append(("Prior clean baseline report", relative_link(ROOT / f"ELABORATION_REPORT_{report_date}_{prior['label'].upper()}.md", output)))
        pointers.append(("Before/after comparison", relative_link(ROOT / f"docs/elaboration/COMPARISON_{report_date}.md", output)))
    if correction:
        for title, filename in (("Original false-invalid metrics", "metrics-original-parser.json"),
                                ("Parser-only correction record", "parser-correction.json"),
                                ("Unchanged timed build log", "build.txt"),
                                ("Original execution setup", "setup.json"),
                                ("Exact original execution script", "execution-measurement-script.py"),
                                ("Exact corrected parser script", "corrected-warning-parser-script.py")):
            pointers.append((title, relative_link(ROOT / f"docs/elaboration/{snapshot['label']}/{filename}", output)))
    sections.append("\n".join(f"- [{title}]({url})" for title, url in pointers))
    return "\n\n".join(sections) + "\n"


def comparison_report(after, before, findings, output, report_date):
    a, b = after["metrics"], before["metrics"]
    gate = comparison_gate(after, before)

    def headline_row(name, before_value, after_value):
        places = 3 if name.endswith("(GiB)") else 0 if name.endswith("(KiB)") else 2
        return (name, fmt(before_value, places), fmt(after_value, places),
                delta(after_value, before_value, places), percent(after_value, before_value))

    lines = ["<!-- Copyright (c) 2026 Jinzhao Wang. Released under Apache 2.0; see LICENSE. -->",
             f"# Elaboration before/after — {report_date}",
             f"Before: `{b['commit']}` after the dead-code sweep. After: `{a['commit']}` after the measured elaboration cleanup. These are separate source snapshots; no numbers below substitute for proof validation.",
             f"The filename date `{report_date}` is the campaign label. Authoritative UTC windows: before `{b.get('started_utc', 'unavailable')}` to `{b.get('finished_utc', 'unavailable')}`; after `{a.get('started_utc', 'unavailable')}` to `{a.get('finished_utc', 'unavailable')}`.",
             table(["Metric", "Before", "After", "Δ", "Relative Δ"],
               [headline_row(name, x, y) for name, x, y in [
                ("Wall (s)", b.get("timing", {}).get("wall_seconds"), a.get("timing", {}).get("wall_seconds")),
                ("User CPU (s)", b.get("timing", {}).get("User time (seconds)"), a.get("timing", {}).get("User time (seconds)")),
                ("System CPU (s)", b.get("timing", {}).get("System time (seconds)"), a.get("timing", {}).get("System time (seconds)")),
                ("Measured CPU: user + system (s)", cpu(b), cpu(a)),
                ("Peak accounted RSS (KiB)", b.get("timing", {}).get("Maximum resident set size (kbytes)"), a.get("timing", {}).get("Maximum resident set size (kbytes)")),
                ("Peak accounted RSS (GiB)",
                 b["timing"]["Maximum resident set size (kbytes)"] / 1048576 if "Maximum resident set size (kbytes)" in b.get("timing", {}) else None,
                 a["timing"]["Maximum resident set size (kbytes)"] / 1048576 if "Maximum resident set size (kbytes)" in a.get("timing", {}) else None),
                ("Summed Built elapsed durations (s; NOT CPU)", b.get("logged_module_elapsed_sum_seconds"), a.get("logged_module_elapsed_sum_seconds")),
                ("Logged implied parallelism", b.get("implied_parallelism"), a.get("implied_parallelism")),
                ("Logged elapsed ms / code line", b.get("logged_elapsed_ms_per_code_line"), a.get("logged_elapsed_ms_per_code_line")),
                ("Compiled own modules", b.get("compiled_own_modules"), a.get("compiled_own_modules"))]]),
             "## Comparability and limits", " ".join(gate["notes"]),
             "The 10% parallelism tolerance is a declared descriptive reporting rule, not an upstream statistical guarantee. Raw wall differences are displayed even when the gate rejects a speedup conclusion. Logged durations are per-module elapsed values; GNU time measures process CPU separately. Each committed input is SHA-bound and checked against Git.",
             "## Warm profiles, matched files"]
    def change(value, old):
        return "unavailable" if value is None or old in (None, 0) else f"{100 * (value / old - 1):+.2f}%"
    elapsed_change = change(a.get("logged_module_elapsed_sum_seconds"), b.get("logged_module_elapsed_sum_seconds"))
    parallel_change = change(a.get("implied_parallelism"), b.get("implied_parallelism"))
    user_change = change(a.get("timing", {}).get("User time (seconds)"), b.get("timing", {}).get("User time (seconds)"))
    system_change = change(a.get("timing", {}).get("System time (seconds)"), b.get("timing", {}).get("System time (seconds)"))
    rss_change = change(a.get("timing", {}).get("Maximum resident set size (kbytes)"), b.get("timing", {}).get("Maximum resident set size (kbytes)"))
    interpretation = "The summed Built elapsed change (**" + elapsed_change + "**) is not a project-speedup percentage: these overlapping per-module durations are not total CPU or wall time. Logged implied parallelism changed **" + parallel_change + "**; " + (
        "it is outside the matched 10% range, so whole-build wall-speedup claims are rejected. " if gate["matched_implied_parallelism"] is False else
        "the comparison gate and single-run limits still apply. ") + "User CPU changed **" + user_change + "** while system CPU changed **" + system_change + "**. The aggregate CPU difference does not isolate proof search. Peak accounted RSS changed **" + rss_change + "**; this is a measured maximum process/child RSS observation, not concurrent-worker memory summed together, and no stable memory-improvement or no-regression claim follows."
    lines.insert(-1, interpretation)
    pb = {p["file"]: p for p in before["profiles"].get("profiles", [])}
    pa = {p["file"]: p for p in after["profiles"].get("profiles", [])}
    lines.append(table(["File", "Before wall", "After wall", "Δ wall", "Before import", "After import", "Δ import"],
        [("`" + name + "`", fmt(pb[name].get("timing", {}).get("wall_seconds")), fmt(pa[name].get("timing", {}).get("wall_seconds")),
          delta(pa[name].get("timing", {}).get("wall_seconds"), pb[name].get("timing", {}).get("wall_seconds")),
          fmt(phase(pb[name], "import")), fmt(phase(pa[name], "import")), delta(phase(pa[name], "import"), phase(pb[name], "import")))
         for name in sorted(pb.keys() & pa.keys())]))
    lines.append(table(["File", "Before typeclass (s)", "After typeclass (s)", "Δ typeclass (s)"],
        [("`" + name + "`", fmt(phase(pb[name], "typeclass")),
          fmt(phase(pa[name], "typeclass")),
          delta(phase(pa[name], "typeclass"), phase(pb[name], "typeclass")))
         for name in sorted(pb.keys() & pa.keys())]))
    lines.append("Compare both increases and decreases in these typeclass elapsed counters. These observations neither establish stable effects nor isolate proof-search CPU or the cause of an increase. The single-intervention screens and their retained/reverted decisions are reported separately.")
    lines.append("Warm commands run serially, but Lean itself can execute tasks in parallel and single per-file samples still contain noise. Retained-intervention A/B repetitions, if any, are documented separately below. Flat `--profile` component counters are exclusive within instrumented stacks; aggregation across threads/tasks can exceed wall time. They do not partition the wall clock, and their sum is not GNU process CPU/wall time. Structured nested profiler traces are separate and may contain overlapping durations as well.")
    before_report = ROOT / ("ELABORATION_REPORT_" + report_date + "_" + before["label"].upper() + ".md")
    after_report = ROOT / ("ELABORATION_REPORT_" + report_date + "_" + after["label"].upper() + ".md")
    lines.extend(["## Heavy-tail policy metric", table(["Tier", "Before", "After", "Δ"],
        [("≥" + t + " s", b.get("heavy_tail", {}).get(t, "—"), a.get("heavy_tail", {}).get(t, "—"),
          delta(a.get("heavy_tail", {}).get(t), b.get("heavy_tail", {}).get(t), 0)) for t in ("10", "20", "30", "40")]),
        "## Measured interventions", findings_text(findings),
        "## Evidence and full reports",
        f"- [Before report]({relative_link(before_report, output)})\n"
        f"- [After report]({relative_link(after_report, output)})\n"
        f"- [Reproduction guide]({relative_link(ROOT / 'docs/elaboration/README.md', output)})"])
    return "\n\n".join(lines) + "\n", gate


def publish_snapshot(snapshot):
    destination = ROOT / "docs/elaboration" / snapshot["label"]
    destination.mkdir(parents=True, exist_ok=True)
    manifest = {"schema": "elaboration-evidence-publication-v1", "measured_commit": snapshot["metrics"]["commit"],
                "original_inputs_sha256": {"metrics.json": snapshot["metrics_sha256"], "profiles.json": snapshot["profiles_sha256"]},
                "privacy_transform": "External process commands omitted; absolute checkout paths replaced by <checkout>, other home paths by <external-path>. Numeric metrics and source hashes retained.",
                "published_sha256": {}}
    manifest["profile_selection"] = snapshot.get("profile_selection")
    for name, value in (("metrics.json", snapshot["metrics"]), ("profiles.json", snapshot["profiles"]),
                        ("committed-analysis.json", snapshot["analysis"])):
        file = destination / name
        file.write_text(json.dumps(sanitized(value), ensure_ascii=False, indent=2) + "\n")
        manifest["published_sha256"][name] = sha(file.read_bytes())
    correction = snapshot.get("parser_correction_verified")
    additional = ["setup.json", "build.txt"]
    if correction:
        additional.extend(["metrics-original-parser.json", "parser-correction.json"])
    for name in additional:
        original_file = snapshot["metrics_path"].parent / name
        if not original_file.exists():
            continue
        data = original_file.read_bytes()
        file = destination / name
        manifest["original_inputs_sha256"][name] = sha(data)
        if name.endswith(".json"):
            file.write_text(json.dumps(sanitized(json.loads(data)), ensure_ascii=False, indent=2) + "\n")
        else:
            # Main logs contain relative project names. Preserve exact bytes
            # when no unrelated absolute home path requires privacy filtering.
            cleaned = clean_string(data.decode())
            file.write_bytes(data if cleaned == data.decode() else cleaned.encode())
        manifest["published_sha256"][name] = sha(file.read_bytes())
    execution_script = git_blob(snapshot["metrics"]["commit"], "scripts/elaboration-test.py")
    script_origin = "measured Git commit's scripts/elaboration-test.py"
    if sha(execution_script) != snapshot["metrics"]["measurement_script_sha256"]:
        replay_script = (ROOT / "scripts/elaboration-test.py").read_bytes()
        if sha(replay_script) != snapshot["metrics"]["measurement_script_sha256"]:
            raise ValueError("Cannot publish an execution script different from its recorded SHA")
        execution_script = replay_script
        script_origin = "working-tree instrumentation copy matching the recorded SHA; mathematical source commit unchanged"
    script_file = destination / "execution-measurement-script.py"
    script_file.write_bytes(execution_script)
    manifest["published_sha256"][script_file.name] = sha(execution_script)
    manifest["execution_script_origin"] = script_origin
    if correction:
        old_line = b'    sorries = [line for line in warnings if "uses \'sorry\'" in line]\n'
        new_line = b'    sorries = [line for line in warnings if re.search(r"declaration uses [`\']sorry[`\']", line)]\n'
        corrected_script = execution_script.replace(old_line, new_line, 1)
        if sha(corrected_script) != correction["analysis_script_sha256"]:
            raise ValueError("Corrected parser script bytes differ from correction record")
        script_file = destination / "corrected-warning-parser-script.py"
        script_file.write_bytes(corrected_script)
        manifest["published_sha256"][script_file.name] = sha(corrected_script)
        manifest["parser_correction_verification"] = correction
    size_file = snapshot["metrics_path"].parent / "size.txt"
    if size_file.exists():
        file = destination / "size.txt"
        file.write_text(clean_string(size_file.read_text()))
        manifest["published_sha256"][file.name] = sha(file.read_bytes())
    (destination / "publication.json").write_text(json.dumps(manifest, indent=2) + "\n")


def publish_supplemental(snapshot, extra):
    destination = ROOT / "docs/elaboration" / extra["label"]
    destination.mkdir(parents=True, exist_ok=True)
    file = destination / "profiles.json"
    file.write_text(json.dumps(sanitized(extra["profiles"]), ensure_ascii=False, indent=2) + "\n")
    manifest = {"schema": "elaboration-supplemental-publication-v1",
        "scope": "Unpaired current top-five diagnostics; not a cold build or paired comparison member.",
        "measured_commit": snapshot["metrics"]["commit"], "main_metrics_input_sha256": snapshot["metrics_sha256"],
        "original_profiles_input_sha256": extra["profiles_sha256"],
        "published_profiles_sha256": sha(file.read_bytes()),
        "profile_selection": extra["supplemental_selection"],
        "privacy_transform": "Absolute checkout paths replaced by <checkout>; external home paths omitted. Numeric metrics and source hashes retained."}
    (destination / "publication.json").write_text(json.dumps(manifest, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--label", required=True)
    parser.add_argument("--metrics")
    parser.add_argument("--profiles")
    parser.add_argument("--supplemental-profiles", help="Separate source-bound current top-five profiles outside the frozen nine; never changes paired comparisons")
    parser.add_argument("--supplemental-output", help="Path for the unpaired supplemental report")
    parser.add_argument("--output")
    parser.add_argument("--prior", help="Prior label, normally before")
    parser.add_argument("--prior-metrics")
    parser.add_argument("--prior-profiles")
    parser.add_argument("--findings")
    parser.add_argument("--date", help="Report date; defaults to the measurement's UTC start date")
    parser.add_argument("--comparison-output")
    parser.add_argument("--publish-inputs", action="store_true")
    args = parser.parse_args()
    if args.supplemental_output and not args.supplemental_profiles:
        parser.error("--supplemental-output requires --supplemental-profiles")
    for label in (args.label, args.prior):
        if label and not re.fullmatch(r"[A-Za-z0-9_-]+", label):
            parser.error("Labels must be simple path-free names")
    snapshot = load_snapshot(args.label, args.metrics, args.profiles)
    supplemental = load_supplemental(snapshot, args.supplemental_profiles) if args.supplemental_profiles else None
    prior = load_snapshot(args.prior, args.prior_metrics, args.prior_profiles) if args.prior else None
    report_date = args.date or str(snapshot["metrics"].get("started_utc", ""))[:10] or datetime.now().date().isoformat()
    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", report_date):
        parser.error("Date must have YYYY-MM-DD format")
    findings = read_json(resolved(Path(args.findings))) if args.findings else None
    output = resolved(Path(args.output or f"ELABORATION_REPORT_{report_date}_{args.label.upper()}.md"))
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(report(snapshot, prior, findings, output, report_date, supplemental))
    print("Wrote " + str(output.relative_to(ROOT)))
    if supplemental:
        supplemental_output = resolved(Path(args.supplemental_output or f"docs/elaboration/SUPPLEMENTAL_TOP_FIVE_{report_date}.md"))
        supplemental_output.parent.mkdir(parents=True, exist_ok=True)
        supplemental_output.write_text(supplemental_text(snapshot, supplemental, supplemental_output, report_date))
        print("Wrote " + str(supplemental_output.relative_to(ROOT)))
    if prior:
        comparison_output = resolved(Path(args.comparison_output or f"docs/elaboration/COMPARISON_{report_date}.md"))
        comparison_output.parent.mkdir(parents=True, exist_ok=True)
        comparison, gate = comparison_report(snapshot, prior, findings, comparison_output, report_date)
        comparison_output.write_text(comparison)
        comparison_output.with_suffix(".json").write_text(json.dumps({
            "schema": "elaboration-comparison-v1", "before_commit": prior["metrics"]["commit"],
            "after_commit": snapshot["metrics"]["commit"], "comparability": gate,
            "raw_input_sha256": {"before_metrics": prior["metrics_sha256"], "after_metrics": snapshot["metrics_sha256"],
                                 "before_profiles": prior["profiles_sha256"], "after_profiles": snapshot["profiles_sha256"]}
        }, indent=2) + "\n")
        print("Wrote " + str(comparison_output.relative_to(ROOT)))
    if args.publish_inputs:
        publish_snapshot(snapshot)
        if supplemental:
            publish_supplemental(snapshot, supplemental)
        if prior:
            publish_snapshot(prior)


if __name__ == "__main__":
    main()
