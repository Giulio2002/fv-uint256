# What a human must review to trust the result

The kernel checks the proofs. What it cannot check is that the *statements* say what you mean. Review these, in this order.

## 1. The specification and the claims

**To see what a function is proven to do, open `lean/Fv256/Spec/<Fn>.lean` (the math) and `lean/Fv256/<Isa>/<Fn>.lean` (the claim).**

* `lean/Fv256/Spec/<Fn>.lean` is pure mathematics on `Nat`/`List` (no Janus, no machine; listed in `scripts/pure-spec.txt` and checked by
  `scripts/check-spec-closure`): the Go signature, the gist in plain words including error and panic cases, and one definition per property, each with a
  comment saying what it captures. A `uint256.Int` is a number below `2^256`; signed variants use two's complement. Shared basics are in `Spec/Basic.lean`.
* `lean/Fv256/{Arm64,Amd64}/<Fn>.lean` is the claim: `Pre` (machine facts only: readable/writable buffers, aliasing, stack, runtime contracts), `Post`
  (results and memory frame, with the results stated through `Fv256.Spec.<fn>`), `theorem correctness : Ensures Extracted.program Extracted.entry ... (Pre ..) (Post ..)`
  and its non-vacuity witnesses. Machine-level helpers shared by claims are in `{Arm64,Amd64}/Machine.lean`.
* A few functions (parsing, formatting, scanning, SSZ) additionally need helper definitions in `Spec/` or in their claim file (for example `Spec/Format*.lean`,
  `Spec/Amd64/`, `Spec/Arm64/`); they are in the statement's closure, so `check-spec-closure` lists them. Implementation-shaped definitions that only the proofs use (for example `fromBE`, `addmodSpec`) live in `lean/Fv256/Proofs/Legacy/`, outside every statement.
* The proofs (`lean/Fv256/Proofs/`) are never part of a statement: `scripts/check-spec-closure` elaborates each statement with proofs replaced by `sorry` and fails
  if a reachable `Fv256` constant is defined outside `Spec/` or a claim file; `Spec/` may not import `Proofs/`.
  `Proofs/Common/SpecChecks.lean` has small kernel-decided sanity examples of the specification.

## 2. The main theorem statements

For each row, the theorem named `Fv256.<Arm64|Amd64|Amd64v3>.<Fn>.correctness` in the row's claim file (`lean/Fv256/<ISA>/<Fn>.lean`); its proof term is
`correctness_proof` from `lean/Fv256/Proofs/<ISA>/<Fn>.lean` (or `<Fn>Main.lean`; see `docs/COVERAGE.md`). `janus verify` prints the statement it checked in a clean
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

A theorem with an unsatisfiable precondition, or with contract hypotheses no code can meet, proves nothing. Janus therefore refuses to verify a main theorem
without a paired, kernel-checked witness, and the witness rules are frozen in Janus `docs/SOUNDNESS.md` (U-WITNESS-RUN, U-WITNESS-CALLSITE, U-WITNESS-PAIR).

* **What `Witness.nonvacuous` (in the claim file) states.** Not merely that some state satisfies the precondition. It is, with the main theorem's binders turned into `∃`:

  `∃ binders, hyps ∧ RetAddr ∧ CallSetup ∧ pre ∧ Returns (program.link impl).withExit ret ... (ABIReturn ∧ post)`

  that is, a kernel-checked **returning run** from a state that satisfies the precondition, meeting the postcondition, tied by unification to the same
  variables and the same hypotheses as `correctness`. The hypotheses are jointly satisfiable by concrete code, and a real run exists.
* **Call-site conjuncts.** Every runtime-contract hypothesis additionally needs a conjunct in the same witness: a state at the call's entry pc that satisfies the
  contract's call precondition (at the same variables). No contract hypothesis can hold vacuously (empty precondition, sizes pinned out of range, `P := False`).
* **Strict pairing.** Janus refuses any main theorem without its paired witness: pairing is by name, `Witness.nonvacuous` with `correctness`, `Witness.<X>` only with
  the main theorem `<X>`; a witness never vouches for another main. A main whose conclusion is only a panic, fault or trap needs a tied second instance.
  Therefore `WITNESS=0` in `verify-all.sh` cannot produce a release result: Janus rejects the row, and the run is only usable for development of the proofs.
  `verify-all.sh` finds the witness theorems with `scripts/witness-theorems.py` and passes each with `--theorem`; `check-spec-closure` also covers the witness statements.
* **Extra witnesses** (`Witness.hex`, `Witness.big`, `Witness.nil`, `Witness.unquoted`, ...) are kernel-checked lemmas about additional paths. They are not audited
  witnesses: they show those paths are inhabited but gate nothing.
* **Limit (KA1).** A witness shows that SOME run returns and that each contract's call precondition is inhabited; it does not show that every contract call is
  reachable on that run (see Known limitations).

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

* **Path reachability (KA1).** Path reachability is not required: the witness exhibits, per contract hypothesis, a state at the callee's entry satisfying the
  contract's call precondition, and a returning run of the whole theorem, but it does not show that the caller's path reaches the call with those arguments.
  A contract that is vacuous only at the arguments of a call no witness run takes is accepted (Janus `docs/SOUNDNESS.md`, "Known limitation (UP3)").
* **Extraction reachability.** The extractor copies the functions reachable by direct branches; an indirect call it misses is absent from the model and faults
  with `noCode` when reached. That can make a theorem unprovable but cannot make a false theorem provable. The extraction flags per row are in `scripts/contract-flags.sh`.
* **Instance binders.** A main theorem with a class-typed theorem-level binder cannot be witnessed, so Janus never verifies it; the statements in this repository
  have none, and `janus verify` additionally checks that every instance-implicit argument of the printed statement is a registered instance of the clean environment.
* **Binary-specific libraries.** Several library programs (division, decimal, exp, ...) hold the absolute addresses and bytes of this exact harness build; they
  are not relocatable. The SSZ and the simple rows are layout independent. Rebuilding the harness with another compiler or flags requires re-verifying.
* **Architectures and modes.** Single-threaded code only; amd64 is checked for the default `GOAMD64=v1` build, plus the `BitLen` row for `v3`.
  Self-modifying code is not modelled.
* **Resource limits are not proof verdicts.** `arm64 Format` needs a 32G memory cap (`scripts/memcap-overrides.txt`); a cap overrun is a failed run, never a weaker proof.
* The generated `TB`/`FM` parts are machine-generated and live in `Proofs/`; `scripts/check-generated.sh` checks them against their generators.
