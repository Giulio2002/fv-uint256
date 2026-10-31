# fv-uint256

Machine-checked proofs, with [Janus](https://github.com/Giulio2002/Janus) (Lean 4), that the **compiled arm64 and amd64 machine code**
of the exported functions and methods of [holiman/uint256](https://github.com/holiman/uint256) computes what an independent
mathematical specification says.

`COVERAGE.md` lists every exported symbol with its status per ISA (`verified`, `todo`, or `blocked` with the exact reason).
Nothing is claimed for a symbol that is not `verified` there.

## Pinned inputs
| input | value |
|---|---|
| uint256 | tag `v1.3.2`, commit `a17fcfb6f8b0245533928fa96aace2cd4c2e9b18` (pure Go, no assembly) |
| Janus | `8304911078076875d0007cf0dc03677a05e19c8a` (`lean/lakefile.toml`, `lean/lake-manifest.json`) |
| Go toolchain | `go1.26.0` (`GOTOOLCHAIN`), `CGO_ENABLED=0`, `-trimpath`; Lean `v4.34.1` |

## Spec vs impl
* **Spec** (`lean/Fv256/Spec.lean`): plain mathematics on `Nat`, a `uint256.Int` is a number `< 2^256`
  (`+`, `-`, `*`, `/`, `%`, shifts, comparisons modulo `2^256`, signed variants through two's complement). It is written
  without reference to the Go code or to any ISA.
* **Impl**: the instruction bytes of the library function, copied by `janus extract` out of the linked linux/arm64 or
  linux/amd64 executable (`go/cmd/harness` links every exported function). Lean decodes and runs them in its ISA model.
* **Theorem** (`lean/Fv256/<Arm64|Amd64>/<Fn>.lean`): `correctness` says that for every admissible call (any caller, any
  other register or memory content, pointer aliasing as stated in the precondition) the code returns without faulting or
  panicking, obeys the Go ABI, and leaves results and memory exactly as `Fv256.Spec` says. The bridge between the two is only
  the memory layout (`val256`/`valueAt`: 32 bytes read as a little-endian number, i.e. four `uint64` limbs).
  Each theorem module also holds `Witness.nonvacuous` (a concrete call satisfies the precondition, so it is not contradictory)
  and `Witness.returns` (that call reaches the claimed result).

## Trusted base
Janus's kernel and audit (the verifier, the ELF byte copy, the Lean models of arm64 and amd64), the Lean kernel and
`leanchecker`, Janus's SHA-pinned runtime contracts (only where a proof calls into the Go runtime), and the Go compiler/linker
as an *input*: we verify the produced binary, not the compiler. Single-threaded code only. Axioms allowed: `propext`,
`Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`.

## Reproduce
```sh
git clone https://github.com/Giulio2002/Janus && git -C Janus checkout 8304911078076875d0007cf0dc03677a05e19c8a
(cd Janus && go build -o bin/janus ./cmd/janus)
JANUS=$PWD/Janus/bin/janus scripts/verify-all.sh          # every function marked verified, both ISAs, summary table
JANUS=... scripts/verify-all.sh IsZero And                 # a subset
```
Needs Go, `bubblewrap`, elan (Lean 4.34.1). See `HOWTO.md` for the single-function commands.
Developing against a local Janus checkout: temporarily replace the `[[require]]` in `lean/lakefile.toml` by
`path = "/path/to/Janus"` (never commit that).
