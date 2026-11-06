# NOTES-B5 (FV-B5, arm64 Reciprocal) -- worktree /srv/fv-uint256-wB5, branch fv/wb5

## Done (all compile, no sorry)
- lean/Fv256/Arm64/: RecipDefs (RecPre, RecRegs, RecMem + RecMem.write, r0f, bv_eq_ofNat), RecipNat (clz facts, word_or/word_lt/top_ge),
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
