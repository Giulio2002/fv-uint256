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

## Toolchain, commands and environment (moved from the README)

| component | version |
|---|---|
| Lean | `leanprover/lean4:v4.34.1` (`lean/lean-toolchain`) |
| Janus | pinned in `lean/lakefile.toml` (`rev`, with `lean/lake-manifest.json`) |
| Go | `go1.26.0` (`GOTOOLCHAIN=go1.26.0`, `CGO_ENABLED=0`, `-trimpath`); the harness hashes are pinned in `scripts/harness.sha256` |
| Other | `python3`, GNU `time`, `memcap` (per-row memory cap used by `verify-all.sh`), `lake` |

You need a built `janus` binary (`go build ./cmd/janus` in the Janus repository, or a release binary) and pass it as `JANUS=/path/to/janus`.

`make help` lists the entry points of the `Makefile`:

| command | what it does |
|---|---|
| `make build` | `lake build` of the `Fv256` library (the extraction-independent modules: specification and lemmas) |
| `make verify` | `scripts/verify-all.sh`: build the harness, extract and `janus verify` every row (arm64, amd64, amd64v3) |
| `make verify FN=Add` / `make verify ISA=arm64` | one function / one ISA |
| `make audit` | audit only (`JANUS_STOP_AFTER_AUDIT=1`: the statement audit without the kernel replay of the proofs) |
| `make lint` | `RELEASE=1 scripts/no-sorry.sh`: no `sorry`/axioms/`native_decide`, source and Lean-level lints, spec-closure check, generated-module check |
| `make check-generated` | generated proof modules equal their generators' output |
| `make clean` | remove `build/` |

Environment: `JANUS` (path of the janus binary), `JANUS_CACHE_DIR` (must be a fresh empty directory for a release run), `ROWS`
(rows verified in parallel, default 1), `MEMCAP` (per-row memory cap, default 24G), `PER_FN_TIMEOUT`. See the header of `scripts/verify-all.sh`.
A full run takes many hours; a single row takes minutes to about an hour.

## Scope and statement details (moved from the README)

* Library: `github.com/holiman/uint256` master `48f3f44` (`v1.3.3-0.20261018174624-48f3f4483d41`), built by the harness in `go/`.
* Scope: 146 exported functions and methods, each on linux/arm64 and linux/amd64, plus one extra amd64 row for the `GOAMD64=v3` build of `BitLen`.
* For every row, `correctness` says: for every admissible call (any caller, any other register or memory content, aliasing as stated in
  the precondition) the code returns without faulting or panicking, obeys the Go ABI, and leaves results and memory exactly as the
  specification (`lean/Fv256/Spec/<Fn>.lean`, plain mathematics on `Nat`) says. Each main theorem is paired with a kernel-checked `Witness.nonvacuous`:
  a returning run from a state satisfying the precondition (and a call-site state for every runtime contract), so the statement is not empty; Janus refuses a theorem without it.
* The instruction bytes are copied by `janus extract` out of the linked executable; Lean decodes and runs them in its ISA model.
  Janus's kernel replay and audit check every theorem.
* `scripts/check-spec-closure` proves, with Lean itself, that every final theorem statement depends only on `Spec/`, the claim files, Janus and the extraction; `Spec/` never imports `Proofs/`.
* Release run (2026-11-13, Janus v0.3.2 `ed896f6d` = gated `8ee31d4d` + CHANGELOG, binary sha256 `671e9e756eb88b9678883319c4f99bb702371307b1616d60c9d24389a0a952a7`, reproducible, the exact binary used; the run's tree pinned v0.3.1 `1b51b4ac`, whose Lean framework is identical: v0.3.2 changes only Go code): fresh-cache full run 31,101 s (8.6 h) wall with 6 rows in parallel at nice +15; every row log shows `Non-vacuity: shown by`; release no-sorry clean.
* Release run (2026-11-12, Janus v0.3.1 `1b51b4ac`, verified on `5355cc4f` = same framework and binary, binary sha256 `d75d7ab7268898d0c2fdd79c0e0cbba138728b3c508a4b1420832eec5c9fad73`, reproducible): fresh-cache full run 23,838 s (6.6 h) wall with 6 rows in parallel; slowest row arm64 ISMod 4500 s; every row log shows `Non-vacuity: shown by`; allocation call sites discharge the new descriptor-outside-window conjunct (`other_newobject_pre` for Scan's errorString).
* Release run (2026-11-12, Janus v0.3.0 `0894e931` = gated `99623d5d` + docs, binary sha256 `b23cdc4c106bbbb9b52e222ecad4c63287cd9fb5ef3424fa08334ecef3573dad`, reproducible): fresh-cache full run 31,694 s (8.8 h) wall with 6 rows in parallel (host shared with two other release gates); slowest row arm64 ISqrt 2599 s; every row log shows `Non-vacuity: shown by`; `Add` rows also carry `within`/`atLeast` (17 instructions).
* Release run (2026-11-11, Janus v0.2.0 `9ff22946`, binary sha256 `0127f1e721ae81a85a3e5eb4726e5cb0e791849169b639bb4aab02ac7a79f8fd`, reproducible): fresh-cache full run 15,750 s (4.4 h) wall with 6 rows in parallel, 20.8 h summed (host shared with other jobs); slowest row amd64 Scan 2008 s; every row log shows `Non-vacuity: shown by`.
* Previous release run (2026-11-09, Janus `722bf8ae`) details: fresh-cache full run 3.9 h wall (6 rows in parallel), 17.8 h summed; slowest row amd64 Scan 3443 s. Janus binary built reproducibly
  (`go build -trimpath -buildvcs=false`, Go 1.26.10), sha256 `44d314819d6f9925c90e9f6e4db8866f92dbc152010691e93877f9ad6aadad54`.
