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


## DivMod amd64 on master 48f3f44 (Janus 6365855c)
`correctness` + `Witness.nonvacuous` verified in one `janus verify` run (3180 s wall incl. queueing, LEAN_NUM_THREADS=8). DivModB compile 487 s (baseline for the S7 Apart-facts experiment).

## Family B amd64 on master 48f3f44 (Janus integ/speed15 6365855c, per-extraction chain)
| symbol | proof | verified theorems | wall (heavy-run, incl. queue) | notes |
|---|---|---|---|---|
| Div | Amd64/Div.lean (+DivSum.div_summary) | correctness, Witness.nonvacuous, Witness.returns | 2519 s | y=0 -> 0; master Eq is XOR (xor_ofNat_zero_iff in run list) |
| Mod | Amd64/Mod.lean (+ModSum.mod_summary) | same three | 2637 s | |
| DivMod | Amd64/DivMod.lean, DivModB.lean, DivModW.lean | correctness, Witness.nonvacuous (single run) | 3180 s | non-live NewobjectContract64; DivModB 452-487 s |
| SDiv | Amd64/SDiv.lean (+SDivSum.sdiv_summary) | same three | 2405 s | n or d zero -> 0 |
| SMod | Amd64/SMod.lean (+SModSum.smod_summary) | same three | 2266 s | sign of x; y=0 -> 0 |
Speed debt: all above the 5-min bar; verify wall is dominated by the per-extraction chain rebuild (library form removes it) and by janus64_run leaf closers.

## Speed pass 1 (family B amd64): library-only proofs (Janus 6365855c, warm machine)
Cause of no speedup from the library programs: DivSum/SDivSum/SModSum still imported `Extracted`, so every consumer recompiled the summary chain.
Fix: those modules no longer import `Extracted` (stated over DivProg/ModProg/SDivProg/SModProg), and Div/Mod correctness is derived from the library summary by `EnsuresOf.ensures3` (no chain import).
| symbol | before (s) | after (s) |
|---|---|---|
| SDiv (3 theorems) | 2611 | 192 |
| SMod | 2924 | 12 (module cache) |
| Div | 2519 (1505 with cached chain) | 114 |
| Mod | 2637 (1719) | 240 |
DivMod (2625 s) still imports the chain through DivModB.partB (non-live newobject path); DivModB compile 452-490 s; profile: janus64_run 140-160 s (omega in janus_omega_cap 60-75 s), janus_frame ~35 s, ~290 s of failing `exact` in the mod leaves.
