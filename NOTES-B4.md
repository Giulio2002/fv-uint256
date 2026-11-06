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
- lean/Fv256/Arm64/RecipProg.lean generated (tools/gen_libprog_arm64.py with --fn Reciprocal --fn (*Int).Lsh, 2nd extraction = Lsh); compiles
  (build/lc.sh with absolute path). Namespace Fv256.Arm64.RecipProg, `program`.
- Disassembly: build/recip-arm64.dis (objdump -D -b binary -m aarch64 --adjust-vma=0xb8d80 build/recip-arm64.bin). Landmarks: entry stack check 0xb8d80;
  zeroing of the 5-word result at sp+0x118 (result slot = caller frame, mu written through it); m3==0 -> 0xb9528 (ret, mu stays 0); pow2 test at b8dbc..b8de8
  (orr/and of limbs, cbz -> 0xb9508); s = clz(m3); shift s+0xbf saved at [sp,#176]; bl Lsh at b8e04 (y at sp+0x20..0x3f); stage 1 from b8e08 (ldr x3=y3,
  yh = x3>>32, cmp w4,0x80000000, udiv 2^63/yh; r1 = 2*((r0<<32) - hi(r0*r0*y3)), csel guard at b8e84 cmp x1(=r1|y3<<1)); stage 2 b8e88.. (adds/adcs chain, guard csel b8ee4);
  stages 3/4/5 follow (mul/umulh pairs, adds/adcs/subs/sbcs chains), final compare with 2^574 and decrement, signed shift tail (lsr/lsl/csel, b9470..b9500).
  Register allocation differs completely from amd64 (no spills in the stages), so the amd64 carry-chain lemmas (RecipArith*) cannot be reused verbatim;
  the closed forms (stage3q, stage4V, sqw, etc.) and the python model are the same since the Go source is the same.
- Plan for whoever continues: (1) arm64 liveness tool (like tools/x86live.py) + `gseg.py`-style skeleton using `janus_run` on arm64 (check whether gen_segment.py
  arm64 mode landed on fv/wf); cuts at stage boundaries (about 8-12 segments of 40-60 instructions); (2) SegCompose from fv/wg lean/Fv256/Arm64/SegCompose.lean;
  (3) per-stage carry-chain lemmas as janus_carry equalities to recipR1.. (reuse RecipArith4/5 ideas); (4) Extracted theorem + witness + verify.
