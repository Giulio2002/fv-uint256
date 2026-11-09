# NOTES-B4 (FV-B4, 2026-11-06)

## Math chain: DONE (commit 5f343c2 + 50c9e71), all Extracted-free, no sorry
- lean/Fv256/RecipChainDefs.lean (defs recipModel, recipR1..recipR4, recipTail, recipPow2, yw, rsqw), RecipChain1..4.lean (r1_spec, r2_spec, r3_spec,
  r4pre_spec, r4_spec), RecipChain.lean (`recip_chain`, `recip_lt192`), RecipPow2.lean (`pow2_limbs`).
- Python oracle of the defs: wip-b4/model.py (agrees with tools/recip_model.py; also asserts all per-stage windows). Compile helper: wip-b4/lc4.sh
  (core-only, oleans in wip-b4/ol, not committed).
- LESSON: before calling omega on goals containing 2^k with k >= ~150, run `numr` (RecipChain1) to evaluate literal powers; otherwise kernel deep recursion / minutes.
  `exponentiation.threshold 1024` is set at the top of each file for that reason.
- Spec form for machine layer: post = RecipWeak/RecipOK of `recipModel m` (m = the 4 input limbs); per stage the machine must produce
  recipR1 y, recipR2 y, recipR3 y, recipR4pre y, recipR4 y with y = m << clz(m3); mu = recipTail s (recipR4 y).

## arm64 machine layer: STARTED only (not a one-session job)
- Extraction (Janus 655a23fa = /srv/janus-fvA-pin655/bin/janus; harness /srv/fv-uint256/build/harness-arm64): symbol is `github.com/holiman/uint256.Reciprocal`
  (NOT `(*Int).Reciprocal`); `build/ex-arm64-Recip` (untracked) holds Extracted.lean: Reciprocal 507 words at 0xb8d80, calls `(*Int).Lsh` (0xbcbf0, 77 words),
  stubs panicdivide 0x507a0 / gopanic 0x84400 / morestack 0x88540.
- lean/Fv256/Proofs/Arm64/RecipProg.lean generated (tools/gen_libprog_arm64.py with --fn Reciprocal --fn (*Int).Lsh, 2nd extraction = Lsh); compiles
  (build/lc.sh with absolute path). Namespace Fv256.Arm64.RecipProg, `program`.
- Disassembly: build/recip-arm64.dis (objdump -D -b binary -m aarch64 --adjust-vma=0xb8d80 build/recip-arm64.bin). Landmarks: entry stack check 0xb8d80;
  zeroing of the 5-word result at sp+0x118 (result slot = caller frame, mu written through it); m3==0 -> 0xb9528 (ret, mu stays 0); pow2 test at b8dbc..b8de8
  (orr/and of limbs, cbz -> 0xb9508); s = clz(m3); shift s+0xbf saved at [sp,#176]; bl Lsh at b8e04 (y at sp+0x20..0x3f); stage 1 from b8e08 (ldr x3=y3,
  yh = x3>>32, cmp w4,0x80000000, udiv 2^63/yh; r1 = 2*((r0<<32) - hi(r0*r0*y3)), csel guard at b8e84 cmp x1(=r1|y3<<1)); stage 2 b8e88.. (adds/adcs chain, guard csel b8ee4);
  stages 3/4/5 follow (mul/umulh pairs, adds/adcs/subs/sbcs chains), final compare with 2^574 and decrement, signed shift tail (lsr/lsl/csel, b9470..b9500).
  Register allocation differs completely from amd64 (no spills in the stages), so the amd64 carry-chain lemmas (RecipArith*) cannot be reused verbatim;
  the closed forms (stage3q, stage4V, sqw, etc.) and the python model are the same since the Go source is the same.
- Plan for whoever continues: (1) arm64 liveness tool (like tools/x86live.py) + `gseg.py`-style skeleton using `janus_run` on arm64 (check whether gen_segment.py
  arm64 mode landed on fv/wf); cuts at stage boundaries (about 8-12 segments of 40-60 instructions); (2) SegCompose from fv/wg lean/Fv256/Proofs/Arm64/SegCompose.lean;
  (3) per-stage carry-chain lemmas as janus_carry equalities to recipR1.. (reuse RecipArith4/5 ideas); (4) Extracted theorem + witness + verify.

## arm64 progress (session 2)
- tools/arm64live.py: aarch64 liveness (regs, [sp,#d] 8-byte slots, NZCV) over build/recip-arm64.dis (regenerate: objdump -D -b binary -m aarch64
  --adjust-vma=0xb8d80 build/recip-arm64.bin). `python3 tools/arm64live.py build/recip-arm64.dis [hexaddr ...]`. Flags-dead cut points have small live sets at:
  b8e08 (3 regs+7 slots), b8e88 (6+6), b8eec (7+6), b8ff0 (5+6), b9004..b9008 (5+8), b91f0 (9+9), b9224 (7+9), b93e0 (10+8), b9410 (3+7), b9454 (5+3), b948c, b94fc.
- tools/arm64emu.py: python emulator of the body b8e08..b94fc (start state: y words at sp+32.., s-index 255-clz at sp+176); `run(m)` returns
  addr -> (regs, mem, flags) BEFORE that instruction; verified: final mu words at sp+280.. equal wip-b4/model.py `model(m)` (5 random m).
  Use it to name values at cut points exactly like tools/gnum.py did on amd64 (matching a register to R1/R2/R3/r4pre words).
- Stage map (from emu matching): R1 in x0 after guard csel b8e84 (cut b8e88); R2 = (x7 lo, x0 hi) after csels b8ee4/b8ee8 (cut b8eec); R3 words appear in x1,x2 (+ third) around
  b8ff4..b9000 and are spilled to sp+136,128 (+144) (cut b9004); R3^2 words in x4..x9,x14/x16 (b900c..b90d4: squares + y spills at sp+232..184); r4pre words are
  produced b91ec..b9230 (spilled [104],[96],[88],[80],x4 = limbs 0..4); product r4pre*y accumulates b9240..b93dc; compare with 2^574 via sbcs chain b93e4..b940c
  (mov x0,#0x4000000000000000 at b9404), cond = neg/ngc at b9410; decrement b9414..b9438, csel b9440..b9450; shift tail (adds doubling b9454..b9464, lt csels,
  lsr/lsl/csel) b9468..b94f8 writes mu to sp+280..312; pow2 branch 0xb9508 (mu = [-1,-1,-1,-1, -1>>p]); m3==0 -> 0xb9528.
- Differences to amd64: the Lsh call can probably be run INLINE (77 instructions, n=clz<64 prunes the branches) instead of via a summary: no arm64 Lsh library summary exists;
  results are written to the caller-frame slots sp+280..312 (sp = entry sp - 0x110), no result pointer. Prologue: sp' = sp-0x110, x29/x30 saved at [sp'-8].
- NEXT (not started): arm64 analog of gseg.py (a64seg.py): parse the janus_run state print for arm64 (`setReg`/`regs` function + `writeLE` chain), L<cut> live defs from arm64live,
  segments through Fv256.Arm64.SegCompose (fv/wg lean/Fv256/Proofs/Arm64/SegCompose.lean: seg_trans on ReachesRet), arithmetic lemmas with UtilAM (awc_fst, awc_c, sbc_num) + janus_carry.

## arm64 progress (session 3): first janus_run skeleton
- wip-b4/arm64_skel_seg0.lean: skeleton `seg0` (entry .. b8e08, i.e. through the inline `bl Lsh`) over Fv256.Arm64.RecipProg.program with precondition
  RecPre (lr%4=0, lr<2^56, GuardOK s 0x90, StackOK s 0x118 0x30, x28 apart from window, x0 32 readable bytes apart from window).
  Compile: LEAN_PATH=<framework lib>:build/ol655 lean -Dpp.deepTerms=true (framework = /srv/janus-ops/jcache-shared/v1/framework/3f949a7d48d2680d5332b3c9/.lake/build/lib/lean);
  lean/Fv256/Proofs/Arm64/RecipProg.olean must be in build/ol655 (build/lc.sh <abs path>). State printing works (setReg chain over `s.regs`, `sp`, `flags := addSub ..`, `mem := ((s.mem.writeLE ..)`) —
  easy to parse (cf. tools/gseg.py parse_trace, replace `setRegF`->`setReg`, regs 4 -> `s.sp`).
- OPEN PROBLEM (first thing to fix): `janus_run until [recEntry+0x6c]` and later FAIL with "stuck after 35 instructions ... s.regs 30": the pow2 path (cbz x4 at +0x68 -> ret at b9524)
  is NOT pruned by my hypotheses hnp / hnp2 (stated as `¬ (X).toNat = 0` and `¬ X = 0#64` with X = (m3 &&& (m3-1)) ||| (m2 ||| (m1 ||| m0)) in BitVec.ofNat of readLE, matching the
  printed x4 at +0x68). The `m3 = 0` cbz (hbr : ¬ readLE .. = 0) is pruned fine from hm3. Find the exact shape of the cbz-x4 branch hypothesis (hbr appears in the goal only after the
  step; try `janus_run until [recEntry+0x68]` then `janus_run until [recEntry+0x6c]` with `trace_state`, or state the hypothesis as `(X).toNat ≠ 0` / `X ≠ 0`, or use `BitVec.toNat` of
  the stepped x4 as printed with `pp.deepTerms`), or ask the Janus owner: a repro for "branch on cbz of an OR chain with a hypothesis of the same shape not pruned".
- After that: seg0 postcondition (RecQ0: y words at sp+32..63 = lsh m s, x3 = y3, shift index at sp+176 = 255-clz, regs listed by arm64live at b8e08), then follow the cut list
  in the previous section. All cuts must be at addresses the emulator names (tools/arm64emu.py).
