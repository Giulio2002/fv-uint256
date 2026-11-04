# Coverage, family B (division, modular arithmetic, iterative numerics)

Status values as in `COVERAGE.md`; plus `verified-local-tstack, pending U7 pin` (kernel check needs the large-stack verifier; not counted as verified).
Upstream blockers: `/srv/janus-ops/UINT256-UPSTREAM.md` (U7 = kernel deep recursion when an epilogue load follows a long chain of stores).

| Symbol | arm64 | amd64 | Notes |
|---|---|---|---|
| `uint256.Reciprocal` | blocked U7 | blocked U7 | local `y Int` + `Lsh` call (same pattern as Float64); spec: floor((2^512-1)/m) or one less (measured: exact in ~99.5% of random m) |
| `(*uint256.Int).Float64` | verified, pending Janus pin (deeprec 35083b3f) | verified, pending Janus pin (deeprec 35083b3f; re-checked with f65043ca) | spec `Fv256.B.float64Bits` (SpecB.lean); both ISAs checked with `janus verify` against the unmerged deeprec framework |
| `(*uint256.Int).Div` | todo (needs bits.Div64 summary, U10) | verified, pending Janus pin (deeprec f65043ca) | spec `Fv256.B.divSpec`; amd64 chain udivremBy1/udivremKnuth/udivrem all proven (summaries), Div wrapper theorem compiles; arm64 chain pending |
| `(*uint256.Int).Mod` | todo (needs bits.Div64 summary, U10) | verified, pending Janus pin (deeprec f65043ca) | spec `Fv256.B.modSpec` |
| `(*uint256.Int).DivMod` | todo (needs bits.Div64 summary) | verified incl. non-vacuity witness `Witness.nonvacuous` (Janus integ/speed15 4d43ed7e; correctness 1884 s end-to-end incl. chain rebuild, witness run 51 s with warm cache) | spec divSpec/modSpec; assumes runtime.newobject contract (NewobjectContract64) with a toy allocator witness; z=m or disjoint; branch fv/wb-s15 |
| `(*uint256.Int).SDiv` | todo (needs bits.Div64 summary, U10) | verified, pending Janus pin (deeprec f65043ca) | spec `Fv256.B.sdivSpec`; uses the Div summary proved in-file (DivSum.lean) |
| `(*uint256.Int).SMod` | todo (needs bits.Div64 summary, U10) | verified, pending Janus pin (deeprec f65043ca) | spec `Fv256.B.smodSpec`; uses the Mod summary proved in-file (ModSum.lean) |
| `(*uint256.Int).AddMod` | todo | todo | |
| `(*uint256.Int).MulMod` | todo | todo | |
| `(*uint256.Int).MulModWithReciprocal` | todo | todo | |
| `(*uint256.Int).MulDivOverflow` | todo | todo | |
| `(*uint256.Int).Exp` | todo | todo | |
| `(*uint256.Int).Sqrt` | todo | todo | |

## Known speed debt (family B)
* `Fv256.Amd64.DivModB.partB` (the dominant cost of `(*Int).DivMod` amd64): 1437 s on f65043ca, 1319 s on 50db36a6, 926 s on 4d43ed7e, 504 s on f1d61dc1 (engine gains: overlap forwarding, S3/S3b, janus_exact; consumer closers unchanged). About 295 s is `janus64_run`, about 250 s is `janus_frame` (four leaves of 52-71 s, `omega` over the whole context), about 200 s is the arithmetic closers (one leaf 311 s because `exact mod_congr` unifies `?a % ?b` against a sum with `c * 0` limbs). Consumer-side attempts that did NOT help (all measured on f1d61dc1): `with_reducible exact` in the closers (broke a leaf), `simp only [Nat.mul_zero, Nat.add_zero]` prefix (trace -20%, wall +50%), `clear`+`janus_clear_irrel` before `janus_frame` (no gain), dedicated `mod_leaf_eq`/`div_leaf_eq` lemmas (timeout > 3300 s), `Janus.Amd64.CABI.readLE_32` in the run (917 s). Target 5 min; parked at 504 s pending the engine-side `janus_frame` reordering (S6).

