# Optional named axiom diagnostics

The root `./check.sh` checks every loaded project declaration, including the
supplementary source-correspondence proofs. These files preserve focused
diagnostics outside ordinary library builds:

```sh
./run-lake.sh env lean scripts/audits/FoundationsAudit.lean
./run-lake.sh env lean scripts/audits/StateOrderInterpolationAudit.lean
./run-lake.sh env lean scripts/audits/StateSupportLimitsAudit.lean
```

They contain imports and `#print axioms` commands, with no mathematical
declarations. Lake's default library globs select root modules (`Glob.one`),
and none of these files was imported by the facade. They were already outside
ordinary library builds. The move organizes their 52 focused diagnostics for
explicit execution; no ordinary-build performance saving is claimed.
