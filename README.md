# fv-uint256

**What this is.** [holiman/uint256](https://github.com/holiman/uint256) is the 256-bit integer library used by Ethereum clients. This repository proves,
with [Janus](https://github.com/Giulio2002/Janus) and the Lean 4 proof checker, that every one of its 146 exported functions is correct **as compiled machine
code**, on both arm64 and amd64. The proofs are about the bytes the CPU runs, not the Go source, so a compiler bug or a mistake in the hand-written
assembly cannot hide. You write down what a function should do as a short mathematical spec; the proof checks that the machine code does exactly that for every input.

## A worked example: `Add`

**The spec** is plain math on natural numbers ([`lean/Fv256/Spec/Add.lean`](lean/Fv256/Spec/Add.lean)):

```lean
/-- `z.Add(x, y)` sets `z = x + y` with wrap-around (arithmetic modulo `2^256`) and returns `z`. No error or panic case. -/
def add (x y : Nat) : Nat := (x + y) % 2 ^ 256

example : add (2 ^ 256 - 1) 1 = 0 := by decide   -- wrap-around: the largest word plus one is zero
example : add 2 3 = 5 := by decide               -- small numbers add as usual
```

**The claim** says the compiled arm64 code does that math ([`lean/Fv256/Arm64/Add.lean`](lean/Fv256/Arm64/Add.lean), shortened):

```lean
/-- PRECONDITION: z is a writable and x, y are readable 32-byte buffers; z, x, y are pairwise equal-or-disjoint. -/
def Pre (z x y : BitVec 64) (s : State) : Prop :=
  Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
  Aliasing z x ∧ Aliasing z y ∧ Aliasing x y

/-- POSTCONDITION: X0 = z; the number now at z is Spec.add of the numbers at x and y BEFORE the call; only z[0, 32) was written. -/
def Post (z x y : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  val256 s'.mem z.toNat = Fv256.Spec.add (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
  OnlyWrites s.mem s'.mem z.toNat 32

/-- THE CLAIM: every call meeting Pre returns (Go ABI obeyed) in a state meeting Post. -/
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y] (Pre z x y) (Post z x y) :=
  correctness_proof z x y
```

**How to read it.** The spec is the math: it is the only part that says what `Add` means, so it is the part to review. The claim says that the
machine code extracted from the compiled binary (`Extracted.program`), called with any state satisfying `Pre`, returns without a fault or panic in a state satisfying
`Post`, and `Post` is stated through the spec. The proof (`lean/Fv256/Proofs/`) is machine-checked by Lean's kernel; you do not need to read it. Next to every
claim sits a `Witness.nonvacuous` theorem showing that `Pre` can actually be met and the code really returns, so the claim is not empty.

## Result

All 293 rows verified: 146 functions on each of arm64 and amd64, plus one amd64 `GOAMD64=v3` row. Every main theorem is paired with a kernel-checked
non-vacuity witness, and the release lint is clean. Per-row status: [`docs/COVERAGE.md`](docs/COVERAGE.md).

RESULT-LINE

## Check it yourself

You need Lean (via `elan`), Go, and a `janus` binary (a [release](https://github.com/Giulio2002/Janus/releases) or built from the Janus repository).

```sh
export JANUS=/path/to/janus JANUS_CACHE_DIR=$(mktemp -d)       # janus binary; a fresh empty proof cache
make build                                                     # build the specs and lemmas (lake build)
make verify FN=Add ISA=arm64                                   # extract the compiled Add and check its proof (minutes)
make lint                                                      # no sorry/axioms, spec closure, generated files up to date
make verify                                                    # all 293 rows (many hours; ROWS=6 runs six in parallel)
```

Other variables (`MEMCAP`, `PER_FN_TIMEOUT`) and the toolchain versions are in [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md).

## What you have to trust

* **The specs.** `lean/Fv256/Spec/*.lean` say what each function should do. If a spec is wrong, a correct proof of it is worthless, so these short files are what to read.
* **The claim statements.** The `Pre`/`Post` in `lean/Fv256/{Arm64,Amd64}/*.lean` (and the runtime contracts for calls into the Go runtime, such as memory allocation).
* **Janus.** Its models of the arm64 and amd64 instruction sets, its byte extractor, and the Lean kernel. The Go compiler is not trusted.
* **The exact build.** The result is about the pinned harness binary in `go/` (checked by hash), not about any other compiler version or flags.
* Known limitations (single-threaded model, no timing or side channels, and more) are listed in [`docs/HUMAN-REVIEW.md`](docs/HUMAN-REVIEW.md).

## Repository map

```
docs/      COVERAGE.md (status of every row), HUMAN-REVIEW.md (what to review), DEVELOPMENT.md (toolchain, proof techniques, tooling)
go/        the harness: a program linking every exported uint256 function, whose compiled code is verified
lean/      the Lean package
  Fv256/Spec/     the math for each function (read these)
  Fv256/Arm64/    the claim per function for arm64 (Pre, Post, correctness, witness)
  Fv256/Amd64/    the same for amd64 (Amd64v3/ holds the one GOAMD64=v3 claim)
  Fv256/Proofs/   the machine-checked proofs and generated modules (no need to read)
scripts/   verify-all.sh, the lints, generators and pinned data
Makefile   entry points: make help
```

## More

[`docs/COVERAGE.md`](docs/COVERAGE.md) (every function, every row) | [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md) (toolchain, tooling, proof techniques) | [`docs/HUMAN-REVIEW.md`](docs/HUMAN-REVIEW.md) (what a reviewer must check, and limitations)
