# Coverage, family B (division, modular arithmetic, iterative numerics)

Status values as in `COVERAGE.md`; plus `verified-local-tstack, pending U7 pin` (kernel check needs the large-stack verifier; not counted as verified).
Upstream blockers: `/srv/janus-ops/UINT256-UPSTREAM.md` (U7 = kernel deep recursion when an epilogue load follows a long chain of stores).

| Symbol | arm64 | amd64 | Notes |
|---|---|---|---|
| `uint256.Reciprocal` | blocked U7 | blocked U7 | local `y Int` + `Lsh` call (same pattern as Float64); spec: floor((2^512-1)/m) or one less (measured: exact in ~99.5% of random m) |
| `(*uint256.Int).Float64` | verified, pending Janus pin (deeprec 35083b3f) | todo | proof outline done (wip/); spec `Fv256.B.float64Bits` in SpecB.lean |
| `(*uint256.Int).Div` | todo | todo | lemmas proven, function theorem pending: UtilB.div2by1_correct (Moller-Granlund step), wip/DivWork-amd64.lean by1_loop (udivremBy1 loop, amd64); needs entry summary, udivremKnuth, udivrem, (arm64: math/bits.Div64) |
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
