# NOTES-B5 (FV-B5, arm64 Reciprocal) -- worktree /srv/fv-uint256-wB5, branch fv/wb5

## Done (all compile, no sorry)
- lean/Fv256/Proofs/Arm64/: RecipDefs (RecPre, RecRegs, RecMem + RecMem.write, r0f, bv_eq_ofNat), RecipNat (clz facts, word_or/word_lt/top_ge),
  RecipLive (GENERATED L<off> defs), RecipSeg0 (entry..+0x88 incl. inline Lsh; Q0 = y words + lsh eq + sidx),
  RecipG/G_A_B (GENERATED segments, offsets from entry 0xb8d80; 21 cuts), RecipG/C_*.lean (chains from tools/a64chain.py),
  RecipBridge (ISA-independent copy of B3's bridge lemmas), RecipBv (rot32_shl/rot32_hi/toNat_ite), RecipArith1 (sum1: stage 1 x108r0 = recipR1 Y).
- tools/a64gen.py: `live CUTS`, `seg A B` (runs Lean skeleton with Q = conj of `(reg).toNat = vk`, simp-normalises to Nat, parses witnesses, emits+compiles G_A_B).
  Overrides for branchy segments via OVR/EXTAC (see tools/run88b.py for 0x88->0xbc). ~50-100 s per segment; a 29-instr segment with 40 live vars
  took >20 min -> keep <=17 instrs / <=45 live in the multiply regions.
- tools/a64chain.py NAME cut...: composes consecutive segments into C_A_Z (+json sidecar).
- Cut list (abs): b8e08 b8e3c b8e88 b8eec b8f28 b8fa8 b9004 b9028 b907c b90b4 b90f0 b9110 b9150 b9184 b91c8 b91f0 b9228 b9244 b9264 b9284 b92a4 b92c4 b92e4 b9324 b9354 b9384 b93c8 b9418 b9488 b94fc.
  Chains composed: C_88_108 (b8e08..b8e88), C_16c_284, C_284_390, C_390_4a8, C_4a8_564, C_564_698, C_698_77c; G_108_16c is the stage-2 single segment.
- L defs use `(S.regs i).toNat = v` / `S.mem.readLE (S.sp.toNat + d) 8 = v` (S = current state, sp = entry sp - 272).

## Recipe learned
- cbz branch facts must be in the stepper's Nat form (`m3 &&& (m3-1) ||| (m2 ||| (m1 ||| m0)) = 0`).
- `first | A | B` with nested `by omega` inside rw terms does NOT backtrack (errors are recovered): use `have h : C := (by omega)` as a separate step, or by_cases.
- Normalised eqs can still hold BitVec leftovers (csel `ite` on BitVec, `lsl #32` as rotateRight/&&&): use RecipBv lemmas then Nat.shiftLeft_eq in simp (see RecipArith1).
## TODO
stage 2..5 sum lemmas (sum2 on G_108_16c, sum3 on C_16c_284, sum4 on C_284_390+C_390_4a8, sum5 on C_4a8_564, C_564_698, C_698_77c incl. shift tail),
pow2 path (pc 0xb9508) and m3=0 path, whole-function Summary over Arm64 RecipProg (ReachesRet to s.regs 30; RecMem has saved x29/x30),
Extracted correctness by lib_summary transfer (result at entry sp+8..+48, cf. Arm64/Bytes32), Witness.nonvacuous, ONE janus verify, COVERAGE row to main.


## Update 2026-11-06 ~16:00 (end of FV-B5 session 1; context nearly exhausted -- hand over)
State: branch fv/wb5, worktree /srv/fv-uint256-wB5 (build helpers in build/: lc.sh, ol655 oleans, regen.sh, skel64/ normalised skeleton outputs; NOT committed).
- Segments were REGENERATED with extra normalisers (RecipBv.toNat_ite/rot32 in NORM) and chains recomposed; everything compiles. To regenerate everything: `build/regen.sh` (runs tools/run88b.py for 0x88->0xbc, then `tools/a64gen.py seg A B` for all consecutive cuts; with `skip` the saved skeleton outputs in build/skel64/N2_*.out are reused, ~40 s/segment; without skip each also reruns the Lean skeleton ~100 s). After regenerating segments rerun `tools/a64chain.py x <cuts>` for each chain (var names change) and recompile C_* and RecipArith*.
- RecMem frame is now [(sp-280,sp-8),(sp+8,sp+48)]; RecSpec (Arm64/RecipSpecA.lean) has x18 and that frame; FV-J (arm64 MulMod) consumes `RecipSummary` from there and waits for `theorem recip_summary : RecipSummary` (to be put in Arm64/RecipSummary.lean).
- sum1 (Arm64/RecipArith1.lean) PROVEN: stage 1 x108r0 = recipR1 Y (Y = x88m32+2^64 x88m40+2^128 x88m48+2^192 x88m56).
- sum2 IN PROGRESS (Arm64/RecipArith2.lean, statement drafted): on G_108_16c, claim x16cr7 + 2^64*x16cr0 = recipR2-form (guard: all-ones when raw=0 and 2*y3%M=0). After `simp (disch := first | janus_carry_disch | decide | omega) only [Fv256.AM.dec_le_div, ...] at h_x16cr0 h_x16cr7` the eqs are `if C then x108r1 else LO` / `if C then x108r1 else HI` (same C = (lo'|||hi'|||y3*2 %M = 0), x108r1 = 2^64-1); `unfold stage2e; rw [h_x16cr0,h_x16cr7]; split <;> split` gives 4 cases. Remaining: (a) show lo'+M*hi' = raw128 := (2*(R1*M)+2^128-(2*stage2e R1 y2 y3)%2^128)%2^128 by `janus_carry` in the else/else case; (b) C <-> (raw=0 /\ 2*y3%M=0) via Nat.or_eq_zero_iff and lo',hi'<M. Pure Nat; no more engine issues.
- Then sum3 (C_16c_284: R3 = recipR3 from R2 words), sum4 (C_284_390 + C_390_4a8 -> recipR4pre, words at slots 104,96,88,80 + x4), sum5 (C_4a8_564, C_564_698: products/accumulation, compare with 2^574, conditional decrement, C_698_77c: doubling when n=-1, shift tail: hand-check generated eq texts which already compiled). Use the amd64 lemmas as templates: Amd64/RecipArith3/4*/5* + RecipStage4/5, RecipStage5Lem.lean, RecipShr.lean (ISA independent math; copy and re-namespace as done for RecipBridge). Final bridge to recipModel: lemmas yw_words, lsh_eq_recipY, recipS_eq, clz_log2 are in Arm64/RecipBridge.lean; compose like Amd64/RecipBridge.chain_final but with arm64 stage values.
- Paths still to prove (janus_run from entry, no cuts needed): m3=0 (jumps to 0xb9528: mu stays zero, ret) and pow2 (cbz taken -> 0xb9508: mu = [-1,-1,-1,-1, -1 >> (x3 mod 64)] with x3 = 255 - clz; relate to recipPow2 via Fv256.F.pow2_limbs and RecipBridge). Hypotheses in the stepper's Nat form (see seg0).
- Then Arm64/RecipSummary.lean (case split m3=0 / hz / main path: seg0 -> G_88_bc -> ... -> tail -> ret to s.regs 30; the final ret target: S.regs 30 restored from mem slot sp-272+? (RecMem.2.1 says M.readLE (sp0-272) 8 = s.regs 30) via ldp x29,x30,[sp,#-8]), then Extracted correctness by lib_summary + witness + ONE janus verify (pin 655a23fa, JANUS_CACHE_DIR=/srv/janus-ops/jcache-shared), COVERAGE row to main.
- Gotchas: no Mathlib (no ring_nf/interval_cases); `first | (.. rw [if_pos (by omega)] ..) | ..` does NOT backtrack on nested-by errors: use `have h : C := (by omega)` first; `by_cases` + `exfalso; omega`; use `done`-less closers. Never edit a64gen.py while a batch runs.
