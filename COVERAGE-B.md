# Coverage, family B (division, modular arithmetic, iterative numerics)

Status values as in `COVERAGE.md`; plus `verified-local-tstack, pending U7 pin` (kernel check needs the large-stack verifier; not counted as verified).
Upstream blockers: `/srv/janus-ops/UINT256-UPSTREAM.md` (U7 = kernel deep recursion when an epilogue load follows a long chain of stores).

| Symbol | arm64 | amd64 | Notes |
|---|---|---|---|
| `uint256.Reciprocal` | blocked U7 | blocked U7 | local `y Int` + `Lsh` call (same pattern as Float64); spec: floor((2^512-1)/m) or one less (measured: exact in ~99.5% of random m) |
| `(*uint256.Int).Float64` | verified, pending Janus pin (deeprec 35083b3f) | verified, pending Janus pin (deeprec 35083b3f; re-checked with f65043ca) | spec `Fv256.B.float64Bits` (SpecB.lean); both ISAs checked with `janus verify` against the unmerged deeprec framework |
| `(*uint256.Int).Div` | todo (needs bits.Div64 summary, U10) | proven locally, janus verify running (deeprec f65043ca) | spec `Fv256.B.divSpec`; amd64 chain udivremBy1/udivremKnuth/udivrem all proven (summaries), Div wrapper theorem compiles; arm64 chain pending |
| `(*uint256.Int).Mod` | todo | todo | |
| `(*uint256.Int).DivMod` | todo | todo | extraction needs `--max-functions` (reaches >64 functions via new(Int)/Set) |
| `(*uint256.Int).SDiv` | todo | todo | |
| `(*uint256.Int).SMod` | todo | todo | |
| `(*uint256.Int).AddMod` | todo | todo | |
| `(*uint256.Int).MulMod` | todo | todo | |
| `(*uint256.Int).MulModWithReciprocal` | todo | todo | |
| `(*uint256.Int).MulDivOverflow` | todo | todo | |
| `(*uint256.Int).Exp` | todo | todo | |
| `(*uint256.Int).Sqrt` | todo | todo | |
