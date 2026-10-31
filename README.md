# fv-uint256

Formal verification, with [Janus](https://github.com/Giulio2002/Janus) (Lean 4), of every exported function and method of
[holiman/uint256](https://github.com/holiman/uint256), on arm64 and amd64 machine code.

## Pinned inputs
- uint256: tag `v1.3.2`, commit `a17fcfb6f8b0245533928fa96aace2cd4c2e9b18` (go.sum `h1:a9EgMPSC1AAaj1SZL5zIQD3WbwTuHrMGOerLjGmM/TA=`). Pure Go (no assembly) in this version.
- Janus: commit `83049110` (recorded again when the proofs are final).
- Go toolchain: go1.26.10 (an input: we verify the produced binary, not the compiler).

## Spec vs impl
- Spec: an independent Lean model (`Nat` modulo 2^256 / `BitVec 256`), written without reference to the Go code.
- Impl: the machine code of the pinned library functions extracted from a compiled binary.
- Each function gets a `correctness` theorem (impl behaviour = spec), a Witness (`nonvacuous`) and `returns`.

## Status
See COVERAGE.md (every exported symbol with status). Work in progress.

## TCB
Janus kernel, Lean kernel, Janus's SHA-pinned runtime contracts, Go toolchain as an input.
