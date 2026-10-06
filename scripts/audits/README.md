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
declarations. Moving them avoids repeating their 52 diagnostics in library
rebuilds.
