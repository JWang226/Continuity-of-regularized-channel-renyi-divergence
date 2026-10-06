#!/usr/bin/env python3
# Copyright (c) 2026 Jinzhao Wang. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Jinzhao Wang (AI-assisted formalization)

"""Measure a guarded project-only rebuild or serial warm Lean profiles.

Usage: python3 scripts/elaboration-test.py build LABEL --time /path/to/gtime
       python3 scripts/elaboration-test.py profile LABEL Module/File.lean ...

Requires prepared dependency oleans. Never runs lake clean/update or restores
caches. The build command deletes ONLY this checkout's resolved .lake/build.
Raw evidence and JSON metrics are saved under .lake/elaboration/LABEL.
The size counter is the pinned lean-elaboration-test skill's unmodified script;
prepare it at .lake/autoformalization-skills as described in the reports.
"""
import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parent.parent
TARGETS = ["All", "ChannelContinuity", "QuantumChannelContinuity", "ComparatorChallenges"]
PREFIXES = ("All", "ChannelRenyiContinuity", "ChannelContinuity", "QuantumChannelContinuity", "ComparatorChallenges")
SKILL_PIN = "70bb859295edc2abb9ad81f8f6e31ab2adf8ca07"
ENV = os.environ.copy()
if platform.system() == "Darwin":
    ENV["DEVELOPER_DIR"] = "/Library/Developer/CommandLineTools"


def command(args):
    return subprocess.check_output(args, cwd=ROOT, env=ENV, text=True).strip()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def save(file, data):
    file.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")


def now():
    return datetime.now(timezone.utc).isoformat()


def processes():
    return [line for line in command(["ps", "-eo", "pid,etime,args"]).splitlines()
            if re.search(r"(?:/|\s)(?:lake|lean|lean4export)(?:\s|$)", line)]


def inventory():
    names = command(["git", "ls-files"]).splitlines()
    return {name: sha((ROOT / name).read_bytes()) for name in names
            if name.endswith(".lean") or name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")}


def dependencies():
    # Stat every cached artifact: even an unchanged content hash with a modified
    # timestamp is disclosed as artifact-tree mutation. No dependency deletion.
    result = {}
    for package in (ROOT / ".lake/packages").iterdir():
        cache = package / ".lake/build"
        lib = cache / "lib/lean"
        if not cache.exists():
            continue
        artifacts = {str(p.relative_to(lib)): [p.stat().st_size, p.stat().st_mtime_ns]
                     for p in lib.rglob("*.olean")}
        all_artifacts = {str(p.relative_to(cache)): [p.stat().st_size, p.stat().st_mtime_ns]
                         for p in cache.rglob("*") if p.is_file()}
        if artifacts:
            result[package.name] = {"resolved_lib": str(lib.resolve()), "oleans": artifacts,
                                    "all_artifacts": all_artifacts}
    for required in ("mathlib", "Quantum", "Comparator"):
        if not result.get(required, {}).get("oleans"):
            raise RuntimeError("Required dependency cache is empty: " + required)
    return result


def is_own(name):
    name = name.split(":", 1)[0]
    return any(name == p or name.startswith(p + ".") for p in PREFIXES)


def timing(text):
    fields = {}
    for line in text.splitlines():
        stripped = line.strip()
        for key in ("User time (seconds)", "System time (seconds)",
                    "Percent of CPU this job got", "Maximum resident set size (kbytes)",
                    "Exit status"):
            if stripped.startswith(key + ":"):
                value = stripped[len(key) + 1:].strip().rstrip("%")
                fields[key] = float(value)
        if stripped.startswith("Elapsed (wall clock) time"):
            value = stripped.split("): ", 1)[1]
            parts = [float(p) for p in value.split(":")]
            seconds = 0.0
            for p in parts:
                seconds = seconds * 60 + p
            fields["wall_seconds"] = seconds
    return fields


def build(args, output):
    before = inventory()
    commit = command(["git", "rev-parse", "HEAD"])
    for name, digest in before.items():
        if digest != sha(subprocess.check_output(["git", "show", commit + ":" + name], cwd=ROOT, env=ENV)):
            raise RuntimeError("Commit measured sources and pins first: " + name)
    counter_repo = ROOT / ".lake/autoformalization-skills"
    if command(["git", "-C", str(counter_repo), "rev-parse", "HEAD"]) != SKILL_PIN:
        raise RuntimeError("Size counter checkout must be pinned to " + SKILL_PIN)
    counter = counter_repo / "skills/lean-elaboration-test/scripts/count_lean_lines.py"
    expected_counter = subprocess.check_output(["git", "-C", str(counter_repo), "show",
                                                SKILL_PIN + ":" + str(counter.relative_to(counter_repo))], env=ENV)
    if counter.read_bytes() != expected_counter:
        raise RuntimeError("Size counter differs from pinned upstream bytes")
    size_text = command(["python3", str(counter), commit])
    (output / "size.txt").write_text(size_text + "\n")
    deps_before = dependencies()
    save(output / "dependency-cache-before.json", deps_before)
    size = {}
    for line in size_text.splitlines():
        key, sep, value = line.partition(":")
        if sep and value.strip().isdigit():
            size[key.strip()] = int(value.strip())
    own_build = ROOT / ".lake/build"
    if own_build.is_symlink() or own_build.resolve() != ROOT / ".lake/build":
        raise RuntimeError("Own build subtree is not an ordinary local directory")
    for dep in deps_before.values():
        resolved = Path(dep["resolved_lib"])
        if resolved == own_build or own_build in resolved.parents:
            raise RuntimeError("A dependency uses the proposed invalidation subtree")
    metadata = {
        "schema": "elaboration-measurement-v1", "commit": commit,
        "started_utc": now(), "host": platform.platform(), "cores": os.cpu_count(),
        "time_tool": command([args.time, "--version"]).splitlines()[0],
        "time_binary": str(Path(args.time).resolve()),
        "lean": command(["./run-lake.sh", "env", "lean", "--version"]),
        "targets": TARGETS, "source_sha256": before, "size": size,
        "size_counter_commit": SKILL_PIN, "size_counter_sha256": sha(counter.read_bytes()),
        "measurement_script_sha256": sha(Path(__file__).read_bytes()),
        "git_status_before": command(["git", "status", "--short"]),
        "process_inventory_before": processes(),
        "dependency_olean_counts": {p: len(v["oleans"]) for p, v in deps_before.items()},
        "invalidation": str(own_build), "scheduling": "Lake default; no explicit concurrency override",
    }
    build_cmd = [args.time, "-v", "./run-lake.sh", "--no-ansi", "--no-cache", "build", *TARGETS]
    metadata["command"] = build_cmd
    save(output / "setup.json", metadata)
    print("Invalidating only " + str(own_build), flush=True)
    if own_build.exists():
        shutil.rmtree(own_build)
    print("Project-only timed build; raw output: " + str(output / "build.txt"), flush=True)
    invalid = []
    with (output / "build.txt").open("w+") as log:
        proc = subprocess.Popen(build_cmd, cwd=ROOT, env=ENV, stdout=log, stderr=subprocess.STDOUT,
                                start_new_session=True)
        seen = 0
        while proc.poll() is None:
            time.sleep(0.5)
            log.flush()
            with (output / "build.txt").open() as reader:
                reader.seek(seen)
                lines = reader.readlines()
                seen = reader.tell()
            for line in lines:
                hit = re.search(r"\bBuilt (\S+) \(", line)
                if hit and not is_own(hit.group(1)):
                    invalid.append("Observed upstream compilation: " + hit.group(1))
            if invalid:
                os.killpg(proc.pid, signal.SIGTERM)
                break
        exit_code = proc.wait()
    text = (output / "build.txt").read_text()
    deps_after = dependencies()
    save(output / "dependency-cache-after.json", deps_after)
    if deps_after != deps_before:
        invalid.append("Dependency olean inventory/stat mutation during timed build")
    if inventory() != before:
        invalid.append("Measured own source or pin mutation during timed build")
    files = []
    for hit in re.finditer(r"\bBuilt (\S+) \(([\d.]+)(ms|s)\)", text):
        name, value, unit = hit.groups()
        if not is_own(name):
            invalid.append("Observed upstream compilation: " + name)
        files.append({"module": name, "seconds": float(value) / (1000 if unit == "ms" else 1)})
    times = timing(text)
    logged_sum = sum(f["seconds"] for f in files)
    groups = defaultdict(float)
    for f in files:
        groups[f["module"].split(".")[0]] += f["seconds"]
    warnings = [line for line in text.splitlines() if line.startswith("warning:")]
    sorries = [line for line in warnings if re.search(r"declaration uses [`']sorry[`']", line)]
    allowed = {"ComparatorChallenges/ChannelRenyiContinuity.lean": 3,
               "ComparatorChallenges/MissingProof.lean": 1}
    sorry_census = Counter(line.split(":", 2)[1].strip() for line in sorries)
    for name, count in sorry_census.items():
        if count != allowed.get(name):
            invalid.append("Unexpected sorry warning census: " + name + ": " + str(count))
    for name, count in allowed.items():
        if sorry_census.get(name, 0) != count:
            invalid.append("Missing intentional reference/control warning: " + name)
    jobs = re.findall(r"\[(\d+)/(\d+)\]", text)
    metrics = {
        **metadata, "finished_utc": now(), "exit_code": exit_code,
        "valid": not invalid and exit_code == 0, "invalid_reasons": sorted(set(invalid)),
        "timing": times, "jobs": max((int(n) for _, n in jobs), default=0),
        "compiled_own_modules": len(files), "file_times": sorted(files, key=lambda f: -f["seconds"]),
        "logged_module_elapsed_sum_seconds": logged_sum,
        "logged_sum_is_cpu": False,
        "implied_parallelism": logged_sum / times["wall_seconds"] if times.get("wall_seconds") else None,
        "logged_elapsed_ms_per_code_line": logged_sum * 1000 / size["non-comment code lines"],
        "heavy_tail": {str(t): sum(f["seconds"] >= t for f in files) for t in (10, 20, 30, 40)},
        "namespaces_logged_elapsed": dict(groups), "warnings": len(warnings),
        "sorry_warnings": len(sorries), "sorry_census": dict(sorry_census),
        "errors": len(re.findall(r"^error:", text, flags=re.M)),
        "warning_kinds": dict(Counter(re.sub(r"^warning:.*?:\d+:\d+: ", "", w).split("\n")[0] for w in warnings)),
        "dependency_artifacts_unchanged": deps_after == deps_before,
        "process_inventory_after": processes(),
    }
    save(output / "metrics.json", metrics)
    print(json.dumps({k: metrics[k] for k in ("valid", "exit_code", "timing", "compiled_own_modules", "heavy_tail", "invalid_reasons")}, indent=2))
    if not metrics["valid"]:
        raise RuntimeError("Invalid build measurement; see metrics.json")


def profile(args, output):
    before = inventory()
    deps_before = dependencies()
    collected = []
    for name in args.files:
        rel = Path(name)
        if (rel.is_absolute() or ".." in rel.parts or name not in before or
                not (ROOT / rel).is_file() or rel.suffix != ".lean" or
                ROOT not in (ROOT / rel).resolve().parents or ".lake" in rel.parts):
            raise RuntimeError("Profile a repository-owned .lean file: " + name)
        stem = name.replace("/", "_").removesuffix(".lean")
        outfile = output / (stem + ".txt")
        cmd = [args.time, "-v", "./run-lake.sh", "env", "lean", "--profile", name]
        print("Serial warm profile: " + name, flush=True)
        with outfile.open("w") as log:
            result = subprocess.run(cmd, cwd=ROOT, env=ENV, stdout=log, stderr=subprocess.STDOUT)
        text = outfile.read_text()
        phases = {}
        if "cumulative profiling times:" not in text:
            raise RuntimeError("Missing Lean cumulative profile: " + name)
        cumulative = text.split("cumulative profiling times:")[-1]
        for line in cumulative.splitlines():
            hit = re.match(r"\s*(.+?)\s+([\d.]+)(ms|s)\s*$", line)
            if hit:
                key, value, unit = hit.groups()
                phases[key.strip().rstrip(":")] = float(value) / (1000 if unit == "ms" else 1)
        if not phases:
            raise RuntimeError("Empty Lean cumulative profile: " + name)
        item = {"file": name, "source_sha256": sha((ROOT / rel).read_bytes()),
                "command": cmd, "exit_code": result.returncode, "timing": timing(text),
                "cumulative_phases_seconds": phases, "log_sha256": sha(outfile.read_bytes()),
                "events_over_100ms": [line for line in text.splitlines()
                                      if re.search(r"took [\d.]+(?:ms|s)", line)]}
        item["dependency_artifacts_unchanged"] = dependencies() == deps_before
        collected.append(item)
        save(output / "profiles.json", {"started_sources": before, "profiles": collected,
                                         "sources_unchanged": inventory() == before})
        if result.returncode or inventory() != before or not item["dependency_artifacts_unchanged"]:
            raise RuntimeError("Profile failed or own sources changed: " + name)
    print("Completed " + str(len(collected)) + " serial warm profiles.", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("build", "profile"))
    parser.add_argument("label")
    parser.add_argument("files", nargs="*")
    parser.add_argument("--time", default=shutil.which("gtime") or "/usr/bin/time")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9_-]+", args.label):
        parser.error("Label must be a simple unique name")
    if "GNU" not in command([args.time, "--version"]):
        parser.error("GNU time -v is required; pass --time /path/to/gtime")
    output = ROOT / ".lake/elaboration" / args.label
    if args.mode == "build" and output.exists():
        parser.error("Build label already exists; use a new label")
    output.mkdir(parents=True, exist_ok=True)
    if args.mode == "build":
        build(args, output)
    else:
        profile(args, output)


if __name__ == "__main__":
    main()
