# tools/ (developer helpers, not needed to check the proofs)

Everything here only produces Lean source or runs checkers; every proof is still kernel-checked by `janus verify`
(`scripts/verify-all.sh` is the reproducible entry point).

- `v.sh ISA Fn`: extract (if needed) and `janus verify` one function (`ISA` = arm64, amd64, amd64v3). Edit the `J=` path to your Janus binary.
- `lean2.sh ISA Fn`: run `lean` directly on a theorem module against the newest verify workspace (fast iteration, prints goals of `trace_state`); the workspace must come from a previous `v.sh` of the same function.
- `util1.sh`: compile `Fv256/Spec.lean` and `Fv256/Util.lean` into `build/olean` (needed by `lean2.sh`; edit `JL=` to a Janus lib dir).
- `cov.py Fn...`: mark COVERAGE.md rows from `build/log-<isa>-<Fn>` verdicts.
- `gen2/*.py`: generators of proof files (shift, byte, SetBytes, ...). They write Lean text only.
- Rules learned: never edit `Util.lean`/`Spec.lean` while a `janus verify` runs (stale-input error); write `(by omega)` in parentheses when more tactics follow on the line; `try tac` swallows following lines, write `(try tac)`.
- The scripts contain local absolute paths (Janus checkout, cache); scrub or parametrise them before publishing.
