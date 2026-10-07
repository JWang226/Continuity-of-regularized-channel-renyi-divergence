<!-- Copyright (c) 2026 Jinzhao Wang. Released under Apache 2.0; see LICENSE. -->
# Reproducing the elaboration measurements

The campaign is complete: [dead-code sweep](../DEAD_CODE_SWEEP_2026-10-06.md), first elaboration test, measured cleanup, second elaboration test. Both timed builds succeeded and passed the input/artifact guards; each built 83 owned modules and has all nine paired serial profiles. Four additional after profiles cover the actual current top five. Read the [before report](../../ELABORATION_REPORT_2026-10-06_BEFORE.md), [after report](../../ELABORATION_REPORT_2026-10-06_AFTER.md), [comparison](COMPARISON_2026-10-06.md), and [supplemental report](SUPPLEMENTAL_TOP_FIVE_2026-10-06.md). The verified bundle preserves both measured source versions.

The results are mixed. Wall time was **1,586.74 → 1,616.34 s (+1.87%)**; measured user + system CPU was **2,057.22 → 1,971.08 s (−4.19%)**, comprising user CPU **+4.16%** and system CPU **−12.61%**. Peak accounted RSS rose **2,615,936 → 3,116,208 KiB (+19.12%)**. Summed module elapsed durations fell **14.38%**, but implied parallelism fell **15.94%**, outside the comparison gate's 10% tolerance. These samples do **not** establish an overall project speedup or isolate a proof-search CPU improvement. The separate [fresh proof verification record](../../Verification/cleanup-2026-10-06/README.md) passed all formal checks; performance measurements themselves are not certification.

`2026-10-06` in report and bundle filenames is the **campaign label**. The after build began on `2026-10-07` UTC; each measurement's actual UTC timestamps are authoritative.

These measurements cover **this repository only**. Mathlib, Lean-Quantum and Comparator compiled artifacts are prepared inputs. The measurement tool never runs `lake clean` or `lake update`; it invalidates only this checkout's resolved `.lake/build`, after verifying it is not a symlink and contains no dependency cache. It aborts a timed build that compiles an upstream module or changes upstream artifacts.

## Prepare a fresh checkout

Install the pinned Lean toolchain as explained in [VERIFYING.md](../../VERIFYING.md), then prepare dependency caches before timing:

```bash
git clone https://github.com/JWang226/continuity-of-regularized-channel-renyi-divergence.git
cd continuity-of-regularized-channel-renyi-divergence
./run-lake.sh exe cache get
./check.sh
git clone https://github.com/scottnarmstrong/LeanAutoformalizationSkills.git .lake/autoformalization-skills
git -C .lake/autoformalization-skills checkout 70bb859295edc2abb9ad81f8f6e31ab2adf8ca07
```

The first check may perform one-time dependency setup. This happens **outside** the timed run. The timer checks populated caches and records dependency artifact inventories before and after every measurement. If a cache guard fails, use the repository's normal cache/setup procedure, then start a fresh label; never count an upstream rebuild as this project's elaboration.

Use GNU time, with its `-v` option. On macOS it is commonly named `gtime`; the system `/usr/bin/time` is BSD time and is rejected. Set the path to your installed GNU binary and check its version:

```bash
task_time_binary="$(command -v gtime)"
"$task_time_binary" --version
```

On systems whose `/usr/bin/time` is GNU time, set `task_time_binary=/usr/bin/time`. Both snapshots must use the same GNU binary/version. The published local runs use GNU time 1.10 at `/opt/homebrew/bin/gtime`. If neither exists, install GNU time before measuring; using another timing tool produces a different methodology.

## Run a project-only build and serial profiles

Commit the Lean sources and toolchain/manifest configuration before a measurement. The tool verifies their bytes against `HEAD`; uncommitted documentation does not alter the source-size snapshot. Use a unique label because an existing build-label directory is rejected:

```bash
python3 scripts/elaboration-test.py build repro-current --time "$task_time_binary"
```

The targets are explicitly `All ChannelContinuity QuantumChannelContinuity ComparatorChallenges`. Lake's default library globs select root modules, rather than every submodule: this target list measures the **83-module facade import closure**, including Comparator specifications/negative controls. `QuantumChannelContinuity.SourceCorrespondence` is the one mathematical module outside that cold-build closure. It is measured separately in both serial profile sets, and the final `check.sh` explicitly builds and audits it. The Git tree has 81 solution/support/export modules, three Comparator specification/control modules and five explicitly run scripts/audits, so its 89-file count is larger than the timed closure. Keep this identical cold-build target list when comparing the snapshots.

After the build, profile the selected **own** modules sequentially. This campaign uses exactly nine paired files in both snapshots, listed below, including the supplementary `SourceCorrespondence` module; its direct profile is not included in the cold-build totals:

```bash
python3 scripts/elaboration-test.py profile repro-current \
  QuantumChannelContinuity/SDPCone.lean \
  QuantumChannelContinuity/Schatten.lean \
  QuantumChannelContinuity/TensorChannels.lean \
  QuantumChannelContinuity/FilterAlignment.lean \
  QuantumChannelContinuity/SDPTrace.lean \
  QuantumChannelContinuity/SourceCorrespondence.lean \
  QuantumChannelContinuity/Filter.lean \
  QuantumChannelContinuity/OrderConvexity.lean \
  QuantumChannelContinuity/RegularizationSup.lean \
  --time "$task_time_binary"
```

The actual published samples are recorded in each `profiles.json`. The profiling mode processes its input files one at a time, after their imported project modules have been built. It saves a successful prefix after each file, so a nonempty JSON file does not indicate completion. The renderer requires the exact nine-file set with no duplicates before allowing completed-test or performance-comparison claims; partial, missing or unexpected selections are provisional.

Render the report after the build and all selected profiles finish:

```bash
python3 scripts/elaboration-report.py --label repro-current \
  --date 2026-10-06 --output ELABORATION_REPORT_REPRO_CURRENT.md \
  --publish-inputs
```

Raw local logs and input JSON are under `.lake/elaboration/<label>/`. The renderer writes source-bound JSON evidence under `docs/elaboration/<label>/`; it omits unrelated process command paths and records both original-input and published-file SHA256 hashes. It also preserves the timed build log, original setup and exact execution script. Rendering reads committed Git blobs and validates the complete profile starting source/pin inventory against the measured inventory, plus each profiled leaf hash. It rejects failed profiles, changed source inventories and unverified dependency preservation. Missing profile data can render only a preliminary diagnostic with no improvement conclusion. Rendering does not rebuild Lean or modify proofs.

The first build at `03dde86daf40a3752c273a3017399539e5c7def9` exited successfully, with unchanged sources and dependency artifacts, but the original warning parser falsely marked it invalid: it expected `uses 'sorry'`, while Lean emitted backticks. A one-line parser correction counted the four authorized warnings from the unchanged saved log. **No timing was rerun or altered.** [Original metrics](before/metrics-original-parser.json), [original setup](before/setup.json), [raw build log](before/build.txt), [correction record](before/parser-correction.json) and both exact script versions are retained. The corrected metrics preserve the original execution-script SHA and add the corrected analysis-script SHA. The renderer verifies those roles, the one-line byte replacement, unchanged execution fields, log hash and corrected census before treating the baseline as valid. This narrowly documented correction is allowed in a method comparison; other script changes are not silently treated as identical instrumentation.

## Replay an exact published source snapshot

The measured Lean sources are fixed at these exact commits:

| Snapshot | Commit | Bundle ref |
| --- | --- | --- |
| Before, after the dead-code sweep | `03dde86daf40a3752c273a3017399539e5c7def9` | `refs/elaboration/2026-10-06/before` |
| After, including the retained cleanup | `8765c21753175381a57b29fa9469b35675515b2c` | `refs/elaboration/2026-10-06/after` |

The [measured-snapshot bundle](measured-snapshots-2026-10-06.bundle) preserves these objects and refs even if the publication branch changes. Its prerequisite is `c1042369444d325216ef75e2c7cf866580e2035b`, which must already exist in the clone. Its [manifest](measured-snapshots-2026-10-06.json) records the refs and checksum; the 19,819-byte bundle's SHA256 is `3af08e0c93e4ff08533e1738cdeef278d7139a30b03b30b0e2ad587dd014e53c`. Use a separate clean **full clone** for each snapshot. Verify the checksum and bundle, then fetch its refs **before** detached checkout or loading the renderer:

```bash
python3 - <<'PY'
import hashlib
from pathlib import Path
bundle = Path('docs/elaboration/measured-snapshots-2026-10-06.bundle').read_bytes()
assert len(bundle) == 19819
assert hashlib.sha256(bundle).hexdigest() == '3af08e0c93e4ff08533e1738cdeef278d7139a30b03b30b0e2ad587dd014e53c'
PY
git cat-file -e 'c1042369444d325216ef75e2c7cf866580e2035b^{commit}'
git bundle verify docs/elaboration/measured-snapshots-2026-10-06.bundle
git fetch docs/elaboration/measured-snapshots-2026-10-06.bundle \
  'refs/elaboration/2026-10-06/before:refs/elaboration/2026-10-06/before' \
  'refs/elaboration/2026-10-06/after:refs/elaboration/2026-10-06/after'
git rev-parse refs/elaboration/2026-10-06/before
git rev-parse refs/elaboration/2026-10-06/after
```

The last two lines must print the commits in the table. If prerequisite verification fails, use a full clone containing that public commit rather than ignoring the failure. Recorded source hashes, Lean/GNU-time versions, commands and nine-file profile sets are in the [before metrics](before/metrics.json), [before profiles](before/profiles.json), [after metrics](after/metrics.json), and [after profiles](after/profiles.json).

Start with `task_snapshot=before`; use `after` in the second clone. Preserve the published tool and profile list before checking out a measured commit, because those older commits can predate the final reporting files:

```bash
task_snapshot=before
task_publication_commit="$(git rev-parse HEAD)"
task_replay_commit="$(git rev-parse "refs/elaboration/2026-10-06/$task_snapshot")"
python3 - "$task_snapshot" "$task_replay_commit" <<'PY'
import hashlib
import json
import sys
from pathlib import Path
Path('.lake').mkdir(exist_ok=True)
label, commit = sys.argv[1:]
expected_commits = {
    'before': '03dde86daf40a3752c273a3017399539e5c7def9',
    'after': '8765c21753175381a57b29fa9469b35675515b2c',
}
assert commit == expected_commits[label]
snapshot = Path('docs/elaboration') / label
metrics = json.loads((snapshot / 'metrics.json').read_text())
assert metrics['commit'] == commit
profiles = json.loads((snapshot / 'profiles.json').read_text())['profiles']
Path('.lake/replay-profile-files.json').write_text(json.dumps([p['file'] for p in profiles]))
tool_name = ('corrected-warning-parser-script.py' if metrics.get('analysis_correction')
             else 'execution-measurement-script.py')
tool = (snapshot / tool_name).read_bytes()
expected = metrics.get('analysis_script_sha256', metrics['measurement_script_sha256'])
assert hashlib.sha256(tool).hexdigest() == expected
Path('.lake/replay-elaboration-test.py').write_bytes(tool)
PY
git checkout --detach "$task_replay_commit"
cp .lake/replay-elaboration-test.py scripts/elaboration-test.py
./run-lake.sh build QuantumChannelContinuity.SourceCorrespondence
./check.sh
python3 scripts/elaboration-test.py build "repro-$task_snapshot" --time "$task_time_binary"
python3 - "$task_time_binary" "$task_snapshot" <<'PY'
import json
import subprocess
import sys
files = json.load(open('.lake/replay-profile-files.json'))
subprocess.run(['python3', 'scripts/elaboration-test.py', 'profile', 'repro-' + sys.argv[2],
                *files, '--time', sys.argv[1]], check=True)
PY
git restore --source=HEAD -- scripts/elaboration-test.py
git checkout --detach "$task_publication_commit"
python3 scripts/elaboration-report.py --label "repro-$task_snapshot" \
  --date 2026-10-06 --output "ELABORATION_REPORT_REPRO_$task_snapshot.md"
```

For the second checkout, set `task_snapshot=after`. The copied script is the exact SHA-bound published instrumentation: the corrected parser version for the first snapshot, and the executed version for the second. Execute it as **`scripts/elaboration-test.py` inside the checkout**, since its root is derived from `__file__`; the ignored copy is storage, not an executable location. At the first commit, copying it intentionally changes only the Python warning-analysis line; mathematical sources and pins remain at the recorded commit, and the new run records its actual script SHA. The explicit `SourceCorrespondence` build is needed because the old `check.sh` did not yet include that supplementary module. After measurement, the narrow restore removes that copied Python edit before returning to the publication's renderer; `.lake/elaboration/repro-<snapshot>/` remains intact. If rendering from another checkout, supply `--metrics` and `--profiles` paths to those saved files and fetch the measured-snapshot bundle there as well.

## Cover any new current top-five modules

Keep the nine paired profiles frozen. The completed after build required four extra profiles: `ContinuityAssembly`, `StabilizedSchatten`, `ComplexTraceHolder`, and `TracePowerBounds`. Their [published evidence](after-top-five/profiles.json) passed the same source/exit/artifact guards. They are **unpaired diagnostics**, excluded from the nine-file comparison.

For another run, derive any additional current top-five files from that run's cold-build log after its nine profiles finish. The following reads saved JSON and profiles missing files sequentially under a separate label. The illustrated `after-top-five` label must be unused; change labels/paths for a new replay:

```bash
python3 - "$task_time_binary" <<'PY'
import json
import subprocess
import sys
from pathlib import Path
metrics = json.loads(Path('.lake/elaboration/after/metrics.json').read_text())
frozen = {p['file'] for p in json.loads(Path('.lake/elaboration/before/profiles.json').read_text())['profiles']}
assert len(frozen) == 9
times = {}
for row in metrics['file_times']:
    module = row['module'].split(':', 1)[0]
    times[module] = times.get(module, 0) + row['seconds']
sources = {file[:-5].replace('/', '.'): file for file in metrics['source_sha256'] if file.endswith('.lean')}
top = sorted(times, key=lambda module: -times[module])[:5]
missing = [sources[module] for module in top if sources[module] not in frozen]
print('Actual top five:', top)
print('Separate supplemental files:', missing)
if missing:
    subprocess.run(['python3', 'scripts/elaboration-test.py', 'profile', 'after-top-five',
                    *missing, '--time', sys.argv[1]], check=True)
PY
```

Render extra profiles through the separate supplemental arguments below. They introduce no new cold build or change to the frozen measurement script. The renderer checks their exact expected selection and treats prefixes or unexpected files as incomplete; publication stores them separately under `docs/elaboration/after-top-five/`.

## Render the published before/after report pair

Both measured tests are complete. To regenerate their reports from the local raw evidence, render the before report:

```bash
python3 scripts/elaboration-report.py --label before --date 2026-10-06 \
  --output ELABORATION_REPORT_2026-10-06_BEFORE.md --publish-inputs
```

This campaign's after report requires the separate four-profile supplemental input. Omitting it would overwrite the report with incomplete current-top-five coverage:

```bash
python3 scripts/elaboration-report.py --label after --prior before --date 2026-10-06 \
  --output ELABORATION_REPORT_2026-10-06_AFTER.md \
  --findings docs/elaboration/interventions.json \
  --supplemental-profiles .lake/elaboration/after-top-five/profiles.json \
  --supplemental-output docs/elaboration/SUPPLEMENTAL_TOP_FIVE_2026-10-06.md \
  --publish-inputs
```

The after invocation also produces `docs/elaboration/COMPARISON_2026-10-06.md` and its JSON comparability record. To regenerate reports from evidence already published in Git, first verify/fetch the bundle refs, then use the published paths and omit `--publish-inputs` to preserve the original publication manifest:

```bash
python3 scripts/elaboration-report.py --label after --prior before --date 2026-10-06 \
  --metrics docs/elaboration/after/metrics.json \
  --profiles docs/elaboration/after/profiles.json \
  --prior-metrics docs/elaboration/before/metrics.json \
  --prior-profiles docs/elaboration/before/profiles.json \
  --output ELABORATION_REPORT_2026-10-06_AFTER.md \
  --findings docs/elaboration/interventions.json \
  --supplemental-profiles docs/elaboration/after-top-five/profiles.json \
  --supplemental-output docs/elaboration/SUPPLEMENTAL_TOP_FIVE_2026-10-06.md
```

The primary `--profiles` input remains the frozen nine. Other campaigns may omit supplemental arguments only when their paired profiles already cover their actual current top five.

## Interpret the numbers

- GNU time's user and system fields measure CPU. Lake's `Built (...)` values are **elapsed durations per module**; their sum is not CPU. The reports keep both measures separate.
- Logged implied parallelism is the elapsed-duration sum divided by wall time. The renderer permits only descriptive wall comparisons within a declared 10% parallelism tolerance, with the same timer, pins, targets, host/core count and scheduler, and validated warm-profile inventories. Two contention indicators suppress a wall-speedup or structural conclusion. One run per state is not a statistical guarantee.
- Lean's flat `--profile` cumulative counters are **exclusive component execution times** within instrumented stacks, according to the pinned `Lean.Util.Profile` source. They aggregate threads/tasks whose durations can overlap in wall time; their sum can exceed GNU wall time, and percentages against wall time do not form a 100% partition. The sum is not GNU process CPU or wall time because uninstrumented runtime and rounding can also differ. Structured `trace.profiler` trees are separate and can contain overlapping nested durations as well. Missing labels are not zeroes, and sub-100ms events are incompletely exposed. Unattributed elaboration requires a per-declaration trace before assigning a cause.
- Profile routing selects the largest counter above the >5s and >25%-of-warm-wall screening thresholds and mentions other qualified counters. That ratio is an actionability heuristic, not a measured fraction of wall-clock runtime. The implementation uses [thread-local stack subtraction and global accumulation](https://github.com/leanprover/lean4/blob/v4.29.0-rc6/src/library/time_task.cpp) with a [steady-clock timer](https://github.com/leanprover/lean4/blob/v4.29.0-rc6/src/util/timeit.h).
- GNU time 1.10's RSS output on the measured Darwin host is in KiB; divide by 1,048,576 for GiB. It reports the maximum accounted process/child RSS, rather than the sum of concurrently running workers' memory.
- The retained Hermitian `Module` cache's provider warm A/B peak accounted RSS was **2,008,880 → 2,565,536 KiB (+27.7%)**. The targeted typeclass counter improved, but the phase screen does not establish a global memory improvement or attribute this single-pair RSS increase to the cache alone. See the [before](ab/ab-hermitian-module-before/profiles.json) and [after](ab/ab-hermitian-module-after/profiles.json) provider evidence. The [diagnostic trace guide](trace/README.md) and [trace manifest](trace/manifest.json) preserve the exact probe/result/log hashes behind the closed-class diagnosis; traced diagnostics are separate from the ordinary untraced A/B timing samples. The final cold-build RSS also rose, as reported above.
- The [explicit import-closure audit](import-closure.json) is bound to both exact source commits. Six retained leaves have smaller import closures, while the combined timed union remains **3,584 non-toolchain modules**, including 3,210 Mathlib and 19 Quantum modules. A smaller leaf footprint is structural evidence, not a runtime or memory prediction. The audit lists 185 explicit Lean/Init/Std/Lake boundaries and does not model implicit prelude edges.
- The weighted longest owned import chain and CPU/cores floor are heuristics. They do not predict an achievable build time or include upstream compilation.
- The four authorized `sorry` warnings belong to three Comparator reference bodies and one missing-proof negative control. Extra or missing warnings invalidate the measurement; they are not proof-library gaps.
- The pinned size counter reports the project's legacy files without `module` headers. The test skill's zero-non-module structural criterion is explicitly **not met**; this cleanup does not migrate the module system.
- Other Lean/Lake processes are disclosed, but their presence never gates a build. The filtered before/after snapshots are not a continuous or complete load inventory. Actual source or dependency artifact mutation invalidates a run.
- The first elaboration snapshot is after the dead-code sweep. The comparison measures the later cleanup, rather than estimating the sweep's performance benefit.

The workflows use the pinned [elaboration-test skill](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/70bb859295edc2abb9ad81f8f6e31ab2adf8ca07/skills/lean-elaboration-test/SKILL.md) and [elaboration-cleanup skill](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/70bb859295edc2abb9ad81f8f6e31ab2adf8ca07/skills/lean-elaboration/SKILL.md). Profiling is separate from proof certification: follow [VERIFYING.md](../../VERIFYING.md) for the all-declaration axiom audit, Comparator and independent kernel checks.
