# tools/ (developer helpers, not needed to check the proofs)

Everything here only produces Lean source or runs checkers; every proof is still kernel-checked by `janus verify`
(`scripts/verify-all.sh` is the reproducible entry point).

- `v.sh ISA Fn`: extract (if needed) and `janus verify` one function (`ISA` = arm64, amd64, amd64v3). Env: `FV_ROOT` (repo root, default: parent of tools/), `FV_JANUS` (Janus binary), `FV_CONTRACTS` (extra `janus extract` flags).
- `lean2.sh ISA Fn`: run `lean` directly on a theorem module against the newest verify workspace (fast iteration, prints goals of `trace_state`); the workspace must come from a previous `v.sh` of the same function.
- `util1.sh`: compile `Fv256/Spec.lean` and `Fv256/Util.lean` into `build/olean` (needed by `lean2.sh`; env `FV_CACHE` selects the Janus consumer cache).
- `cov.py Fn...`: mark COVERAGE.md rows from `build/log-<isa>-<Fn>` verdicts.
- `gen2/*.py`: generators of proof files (shift, byte, SetBytes, ...). They write Lean text only.
- Rules learned: never edit `Util.lean`/`Spec.lean` while a `janus verify` runs (stale-input error); write `(by omega)` in parentheses when more tactics follow on the line; `try tac` swallows following lines, write `(try tac)`.
- No absolute paths: everything is relative to `FV_ROOT`; build outputs stay in `$FV_ROOT/build` (so each git worktree has its own).
- Obsolete one-off generators were removed; `gen2/` holds the current ones.

## AddMod / Exp goal-extraction pipeline (FV-F)
- `mkex.py OUT IDX file.lean`: turn the IDX-th `case` of a `trace_state` dump (a janus64_run run with `all_goals trace_state; sorry`) into a standalone `example` (hyps filtered).
- `mkabs.py` / `mkabsG.py`: same, but abstract the `readLE s.mem (v.toNat + k) 8` atoms into Nat variables `sv0..3` / `tv0..3` -> one Extracted-free lemma per goal shape (`AddModShapes.lean`, `AddModShapesG.lean`).
- `genG1.py`, `emitG2.py`, `build_gen.py`: generate the per-goal bullets for AddModGen (no-overflow `gA_i` lemmas, overflow closers with `omega_s`).
- `gen_exploop.py`: ExpLoop2/3/4 from ExpLoop1; `gen_expmain.py`: ExpMain loop-entry blocks.
- Lessons: bullets per goal (no `first | ..` over big contexts); `with_reducible apply`; drop disjointness disjunctions before omega (`omega_s`, `omega_e`) or state them as `Apart`.
