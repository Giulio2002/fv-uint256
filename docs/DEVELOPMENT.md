# Development notes: proof techniques and tooling

This is a short guide for people extending or re-checking the proofs. The status of every row is in `COVERAGE.md`; what to trust is in `HUMAN-REVIEW.md`.

## Workflow for one function

1. Build the harness (`scripts/verify-all.sh` does it; the three binaries must hash to `scripts/harness.sha256`).
2. Extract: `janus extract build/harness-arm64 'github.com/holiman/uint256.(*Int).IsZero' build/ex-arm64-IsZero` with the row's flags (`scripts/contract-flags.sh`).
3. Write the three layers:
   * `lean/Fv256/Spec/<Fn>.lean`: the pure math (`Fv256.Spec.<fn>`), with the Go signature and the gist in a header comment, a doc comment on every def, cheap
     `example ... := by decide` checks; add it to `scripts/pure-spec.txt` (imports only other `Fv256.Spec.*` files).
   * `lean/Fv256/<Isa>/<Fn>.lean`: the claim: `Pre` (machine facts), `Post` (results via `Fv256.Spec.<fn>`, memory frame via `Janus.Spec.val256` / `valueAt`),
     `theorem correctness : Ensures Extracted.program Extracted.entry [args] (Pre ..) (Post ..) := correctness_proof ..` (the outer shape must stay literally
     `Ensures Extracted.program ...`), and `namespace Witness` with `nonvacuous` (and one per extra main) delegating to `Wit`. Shared machine predicates go (hand-written,
     append-only) in `<Isa>/Machine.lean`.
   * `lean/Fv256/Proofs/<ISA>/<Fn>.lean`: `theorem correctness_proof` (same statement) and `namespace Wit`. Proof: `janus_intro hs; janus_run` (arm64) or
     `janus64_intro hs; janus64_run [readLE_32]` (amd64), then arithmetic (`omega`, `janus_carry` / `janus64_arith`). Tactics, generated modules and program
     lemmas stay here; a nicer-shaped Spec than the implementation-shaped one is connected by a bridge lemma proved here.
4. `janus verify build/ex-arm64-IsZero --proof lean/Fv256/Arm64/IsZero.lean --proof-root lean --theorem Fv256.Arm64.IsZero.correctness`, or `make verify FN=IsZero`.
5. Never edit `Spec/`, the claim files or `Proofs/Common/Util*.lean` while a `janus verify` runs: the input goes stale and the run fails.

A claim file `lean/Fv256/<Isa>/<Fn>.lean` holds the final `theorem correctness`; `verify-all.sh` verifies it (the proof it delegates to is in `Proofs/`, possibly `<Fn>Main.lean`).

## Proof techniques worth keeping

* **Normalise to `Nat` first.** For multiplications, rewrite `BitVec` products to `Nat` (`BitVec.toNat_mul`, `readLE8_mod`, ...) so the carry reflection
  procedure (`janus_carry`) applies: an amd64 `Mul` went from over 30 minutes with plain `omega` to about a minute.
* **Name hypotheses by content, never by position** (`Proofs/Common/GrabTac.lean`, `GrabEq.lean`): `grab_const`, `grab_eq st f [i] as h` (finds `st.f [i] = _`),
  `grab_frame_last`, and `clear_frame_imps` (drops the frame implications of a callee summary that otherwise bloat the context). Positional `rename_i` breaks
  whenever an upstream summary gains a hypothesis.
* **`Apart` and `Hid`.** State disjointness as `Apart a n b m` facts and keep them out of `omega` contexts (drop disjunctions before `omega`, or hide the
  apart/bounds hypotheses behind `Nonempty` during `janus_run ... calls [...]` and unhide when the call precondition needs them). A `Hid`-style
  irreducible wrapper did not help where the call precondition needs the hidden facts.
* **Summaries and libraries.** Large functions (division, modular arithmetic, `Exp`, `Sqrt`, decimal parsing) are proved as Extracted-free "library programs"
  (`ChainProg`, `DivProg`, `ModProg`, `ExpProg`, ...) with `Summary` theorems; a row's theorem links them with `codeIn_of_sub` / `lib_summary`. These hold the
  absolute addresses of the pinned harness, which is why the harness hash is checked.
* **Segment the run.** `janus_run until [pc, ...] calls [h]` splits a long run; one proof module per path or per (limb, bit length) keeps each job small
  (`Log10`, `Format`, `AddMod`).
* **Syntax pitfalls.** Write `(by omega)` in parentheses when more tactics follow on the line (`have h : P := by omega; rest` swallows `rest`); write
  `(try tac)`; prefer one bullet per goal over `first | ...` on large contexts; `with_reducible apply`.
* **Deep recursion.** The Janus kernel replay can hit deep recursion for an epilogue load after a long chain of stores; split the run or restate the frame
  as `OnlyWrites2` (result object plus the callee's stack window).
* **Profile before raising a timeout.** `set_option trace.profiler true` on the module; most slow proofs were dominated by a few failing `janus_omega` calls
  or by the first `run until` of a path.

## Tooling

* **Generators.** `scripts/gen-tb-intobig*.sh`, `gen-fm-hex-*.sh`, `gen-fm-intobig-*.sh` produce the `TB` (ToBig) and `FM` (Format) modules as mechanical
  re-targetings of the IntoBig and Hex proofs onto another extraction. The generators were written for a flat layout; `scripts/gen-layout.py` runs them on a
  legacy view built from `Spec/` + `Proofs/` (`scripts/layout-map.json`, `scripts/leansplit.py`) and splits the output back. `scripts/check-generated.sh`
  (`make check-generated`) never writes a tracked file: it regenerates into a temporary copy and diffs. A new `gen-*.sh` must be added to `GEN_ORDER` there.
* **Memory cap.** Every row runs under `memcap` (default `MEMCAP=24G`). `scripts/memcap-overrides.txt` holds per-row overrides (`ISA Fn CAP  # reason`);
  an override raises a resource limit only, and the row is started only when enough memory is free. `scripts/heavy-first.txt` orders slow rows first.
* **Contract flags.** `scripts/contract-flags.sh` maps a function to its `janus extract --contract ...` flags; `scripts/noflags.txt` lists verified rows that need
  none. A verified row in neither list fails the run.
* **Lint layers** (all run by `RELEASE=1 scripts/no-sorry.sh`):
  1. text-level: `sorry`, axioms, `native_decide` (`no-sorry.sh`);
  2. source lint `scripts/lint_source.py`: compile-time execution commands, import hygiene (parsed by Lean's own header parser, `scripts/LintImports.lean`),
     metaprogramming and attributes only in whitelisted files, lakefile and symlink checks. `scripts/tactic-whitelist.txt` is `sha256<TAB>path` for the files
     that define tactics; a hash mismatch fails the release lint. After reviewing a change to such a file run `scripts/lint_source.py --update-whitelist`;
  3. Lean-level lint `scripts/check-lean-lint`: elaborates statements (`scripts/SvyTools.lean`) and rejects IO, system primitives and initializers in any
     `Fv256` declaration;
  4. spec closure `scripts/check-spec-closure` (survey by `scripts/spec_survey.py`): statements depend only on `Spec/`.
  `scripts/test-lints.sh` and `scripts/test-spec-lints.sh` run the bypass attempts in `scripts/lint-tests/` and require every one to be rejected.
* **Audit-only run.** `make audit` sets `JANUS_STOP_AFTER_AUDIT=1`: the statement audit and non-vacuity check of every row without the kernel replay.
* **Fresh cache.** A Janus cache built against another pin or extractor can poison kernel replay, so `verify-all.sh` insists on an empty `JANUS_CACHE_DIR`
  (`ALLOW_WARM_CACHE=1` for development).
