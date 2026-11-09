# What a human must review to trust the result

The kernel checks the proofs. What it cannot check is that the *statements* say what you mean. Review these, in this order.

## 1. The specification: `lean/Fv256/Spec/`

Every definition a final theorem statement depends on lives here (`scripts/check-spec-closure` enforces it by elaborating each statement with
proofs replaced by `sorry` and failing if any reachable `Fv256` constant is defined outside `Spec/`; `Spec/` may not import `Proofs/`).
`Spec/Util.lean`, `Spec/Core.lean` and the family modules (`B`, `C`, `E`, `F`, `I`, `Format`, ...) define the integer model (a `uint256.Int` is a number
below `2^256`; operations modulo `2^256`, signed variants through two's complement) without reference to Go or an ISA. `Spec/Arm64/`, `Spec/Amd64/`
hold the per-row preconditions, postconditions and memory-layout definitions used in the statements.
`Proofs/Common/SpecChecks.lean` has small kernel-decided sanity examples of the specification.

## 2. The main theorem statements

For each row, the theorem named `Fv256.<Arm64|Amd64|Amd64v3>.<Fn>.correctness` in the row's proof module (`lean/Fv256/Proofs/<ISA>/<Fn>.lean`, or
`<Fn>Main.lean` when that module holds the final theorem; see `docs/COVERAGE.md`). `janus verify` prints the statement it checked in a clean
environment (only Janus and the extraction) and re-elaborates it there. Read the printed statement: preconditions (what the caller promises) and the
postcondition (results, frame, panics).

## 3. Runtime contracts and assumptions

These are hypotheses or pinned trusted objects, stated in the theorem or printed in the `Runtime contracts assumed` banner of `janus verify`:

* **Runtime calls covered by pinned Janus contracts** (`janus extract --contract ...`, per row in `scripts/contract-flags.sh`):
  `runtime.newobject`, `mallocgc`, `makeslice`, `growslice`, `memmove`, `slicebytetostring`, `stringtoslicebyte`, `concatbyte3`, `convTstring`, `convT64`,
  `cmpstring`, `ifaceeq`, `gcWriteBarrier1/2`, `gopanic`. They live in the pinned Janus (`Janus.Contracts.*`, documented in Janus `docs/SOUNDNESS.md`,
  section Runtime contracts). Rows that use them state them as hypotheses over the extracted program (allocation contract, live-allocation contracts).
  Omitted unpinned callees (for example `fmt.errorf`) are not assumptions: no code is copied, the statement says nothing about them, and reaching one
  is a fault, so a closed proof shows the precondition excludes that path.
* **Package-init facts** `InitDone` / `PanicInit` (`Proofs/Amd64/FromDecimalSpec.lean` and the corresponding arm64 modules): the sentinel error values
  (`io.EOF`, `ErrBig256Range`, ...) are initialised and their type words are readable; used by the error paths of the parsing functions.
* **Writable global tables** (`Log10`): `uint256.pows64` and `uint256.pows` live in writable `.noptrdata`, so the statement assumes (`Tabs64`, `TabsBig`
  in `L10Defs.lean`) that they still hold the powers of ten and are readable. A program that mutates them voids the result.
* **Slice invariant** (`WriteToSlice`, ...): `len <= cap` is assumed (only ill-formed slices are excluded).
* **Single-threaded execution, non-moving heap, the Go ABI and the harness binary** (Janus assumptions; see Janus `docs/SOUNDNESS.md`, "Assumptions and limits").
* **Partial scope**: `MarshalSSZAppend`, `MarshalSSZInto` and `UnmarshalSSZ` are complete for the stated scope (for example `len + 32 <= cap`, the success
  path) and say nothing about the other paths. Check the precondition of each.

## 4. The non-vacuity witness rule

A theorem with an unsatisfiable precondition proves nothing. Every `correctness` theorem is accompanied by existential witness theorems (`Witness.nonvacuous`:
a concrete state satisfies the precondition; `Witness.returns`: the call reaches the claimed result; some rows have more, for example `Witness.hex`). `verify-all.sh`
finds them with `scripts/witness-theorems.py` and passes each to `janus verify --theorem`; Janus enforces its witness rule on them. `check-spec-closure` also covers the witness statements. A row without its witnesses fails the run (`WITNESS=0` disables it
for development only, never for a release).

## 5. The Janus trusted computing base

The ISA models (arm64, amd64), the extractor's byte copy, the audit and the kernel replay, the pinned runtime contracts, and the Lean kernel are Janus's.
Its trust boundary is documented in Janus `docs/SOUNDNESS.md` ("Trusted computing base", "What a theorem about Returns / Ensures says", "Assumptions and limits").
The Go compiler and linker are an input: the binary is verified, not the compiler. The Janus revision is pinned in `lean/lakefile.toml`.
Axioms allowed in the proofs: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide` (`scripts/no-sorry.sh`).

## 6. What the repository checks mechanically (so you need not read every proof)

* `scripts/no-sorry.sh` (release mode): no `sorry`, no extra axioms; source lints (`scripts/lint_source.py`: no compile-time execution, no `prelude`/`import all`,
  imports only from `Fv256`/`Janus`/`Extracted`/`Lean`/`Std`/`Init`, tactic/macro/syntax definitions only in the hash-pinned files of `scripts/tactic-whitelist.txt`,
  lakefile restrictions); Lean-level IO/initializer lint (`scripts/check-lean-lint`); spec closure (`scripts/check-spec-closure`); generated modules equal their
  generators (`scripts/check-generated.sh`); the lints are themselves regression-tested (`scripts/test-lints.sh`, `scripts/test-spec-lints.sh`).
* `verify-all.sh` refuses to run on a harness binary whose SHA-256 differs from `scripts/harness.sha256`.

## 7. Known limitations

* **Path reachability (KA1).** The extractor copies the functions reachable by direct branches from the entry; an indirect call it misses is absent from the
  model and faults with `noCode` when reached. This can make a theorem unprovable but cannot make a false theorem provable (Janus `docs/SOUNDNESS.md`).
  The extraction flags per row are in `scripts/contract-flags.sh`.
* **Instance binders.** `janus verify` checks that every instance-implicit argument in the printed statement is a registered instance of the clean environment or
  an instance binder of the theorem. A statement with extra instance binders is read as quantifying over them: review the binders printed in the statement.
* **Binary-specific libraries.** Several library programs (division, decimal, exp, ...) hold the absolute addresses and bytes of this exact harness build; they
  are not relocatable. The SSZ and the simple rows are layout independent. Rebuilding the harness with another compiler or flags requires re-verifying.
* **Architectures and modes.** Single-threaded code only; amd64 is checked for the default `GOAMD64=v1` build, plus the `BitLen` row for `v3`.
  Self-modifying code is not modelled.
* **Resource limits are not proof verdicts.** `arm64 Format` needs a 32G memory cap (`scripts/memcap-overrides.txt`); a cap overrun is a failed run, never a weaker proof.
* The `Spec/Arm64`, `Spec/Amd64` modules and the generated `TB`/`FM` parts are machine-generated; `scripts/check-generated.sh` checks them against their generators.
