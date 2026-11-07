# NOTES-B2 (FV-B2, 2026-11-06): Reciprocal amd64 -- exact state for the next worker
Branch fv/wb-master, worktree /srv/fv-uint256-wBm. Read NOTES-B.md section "FV-B2 session" first (pipeline + janus_carry rules).
Env: build/lc.sh, build/mkol.py are untracked helpers (LEAN_PATH = /srv/janus-ops/jcache-shared/v1/framework/3f949a7d48d2680d5332b3c9/.lake/build/lib/lean : build/ol655). Recreate if build/ is gone; olean cache dir build/ol655.
## Cut list (build/runall.sh CUTS, = RecipLive.lean cuts)
14c 160 1c1 1d0 1f3 273 30d 3bb 3f0 43c 4ca 502 549 5e2 660 689 6b3 6e3 723 74b 776 7ae 801 886 92d 9d4 a06 a49 a71 ab4 ae4 b27 b47 b9f bed c49 d1b (offsets from recEntry). All G_A_B segments compile except c49->d1b (shift tail, 2 goals).
## Stage map and status (word = 64 bit, M = 2^64)
- stage1 (seg0/seg1, done earlier): RecQ1 at +0x14c. RecipStart.start14c bridges RecQ1 -> L14c + Start14c facts.
- stage2 +0x14c..+0x1f3: C_14c_1f3, sum2 (RecipArith2) PROVEN: r2 lo/hi vs r1c/stage2e/all-ones guard (disjunction form).
- stage3 +0x1f3..+0x43c: C_1f3_43c. sum3 (RecipArith3): V = stage3q (proved, 90 s) and r3 = 2*(((R2*2^192+2^320-V)%2^320)/2^128)%2^192 PROVEN (sbb part is lemma sbb3 in RecipArith3s.lean).
- stage4 +0x43c..+0x801: sum4a (squaring words w1..w5 = sqw R3 i, w0*y3 pair) in RecipArith4; sum4p (RecipArith4p) products lo+M*hi = w*y (chain 502..660); sum4q (RecipArith4q) accumulation V_words = sum w_i y_j M^(i+j-3) EXACT (chain 660..7ae; pair vars substituted by w*y%M and w*y/M); sbb4 (RecipArith4s.lean, standalone test) r4pre = (r3*2^256+2^448-V)%2^448/2^128 (chain 7ae..801). STILL TO DO: glue lemmas (instantiate pair equations from sum4a/4p into 4q hypotheses; combine into one stage-4 summary over C_43c_801).
- stage5 +0x801..+0xc49 (adjust): sum5p (RecipArith5p) products r4pre words x y (chain 801..9d4), sum5q (RecipArith5q) accumulation P_words = sum w_i y_j M^(i+j) EXACT (chain 9d4..b47), compare b47..b9f: NOT DONE (cond = [2^574 < P]: rdx=1 iff 2^62 < r13 + borrow-chain, prove via pos_toNat + omega), decrement b9f..bed: sum5d (RecipArith5d.lean, PROVEN: out + cond = r4pre or (r4pre=0, cond=1, out=2^320-1)), bed..c49: doubling when rcx msb (n=-1), NOT DONE.
- tail c49..d1b (signed 5-word shift by n=62-s; n=-1 means 2*R): skeleton has 2 goals; needs a hand segment lemma.
- Not started: m3=0 path (+0x44 je 0xd70: mu stays 0), power-of-two path (+0x72 je 0xd25: mu[0..3]=2^64-1, mu[4]=(2^64-1)>>(p&63)), the call into Lsh already done in seg0, final add rsp/pop/ret, summary theorem over RecipProg, Extracted-level transfer (lib_summary), witness, one janus verify; math chain (below); arm64.
## Math chain (pure Nat; RecipMath/RecipStages already have stage1..4, adjust, mu_window, stage2e_win, stage3q_win, T2win, T3win, d0win, T1win)
1. r1c window |2^319 - r1*y| <= 2^260: r0 = r0f, t1 = r0^2 y3/M, special y3=2^63 gives r1 = M-1 (window by direct calc, y < 2^255+2^192).
2. stage 2 integer R2int = 2 r1 M - 2e with e = stage2e r1 y2 y3: window via stage2/T2win (hd: 2^64 * stage1 window). No-wrap: R2int*y <= 2^383 + 6*2^256; for y3 > 2^63 gives R2int < 2^128; for y3 = 2^63: r1 = M-1, R2int = 2^128 - 2t, t=(2^63+(M-2) y2)/M (y2=0 -> guard all-ones, window by direct calc).
3. stage 3: (r3 + 2K) = 2*R2*M mod 2^192 with K = ceil(V/2^128), V=stage3q; T3win; no-wrap r3int < 2^192 via ONE-SIDED bound r3int*y <= 2^447 + 2^132 and y >= 2^255+1.
4. stage 4: stage4 lemma with u=r3, D = low pairs sum < 2^258, K=ceil(V/2^128): r4pre*y in [2^574 - y - 2^200, 2^574 + 2^200].
5. adjust lemma then mu_window (needs m not a power of two; mu = r4'>>(62-s) for s<=62, 2*r4' for s=63).
## janus_carry rules (essential)
- Prove exact closed forms by `subst h_x..; janus_carry`. Never use independent (lo,hi) atoms of products when overflow-freedom is needed: use w,y atoms and lo := w*y%M, hi := w*y/M.
- `(decide (0<z)).toNat` -> `pos_toNat` (RecipArith2). `decide (a<b)` with b<=1 -> `b - a` (hdl2 in RecipArith5d).
- omega with `% 2^320` or many mod hypotheses in context times out: clear hypotheses, use per-word step lemmas (`wstep`).
## Final state update (end of FV-B2 session)
- PROVEN, committed (HEAD after 233bc34 + "sum5c"): sum2, sum3 (incl. sbb3 in RecipArith3s), sum4a, sum4p, sum4q, sbb4 (RecipArith4s, standalone), sum5p, sum5q, sum5c (compare: rdx = [2^574 < P], RecipArith5c, standalone, 3 s), sum5d (decrement, RecipArith5d, standalone).
- Standalone lemmas (sbb4, sum5c, sum5d) still need to be instantiated against the chain post (use tools/gsum.py or the pattern in RecipArith3.lean: obtain, then `exact lemma <vars> <h_x…>`; clear/avoid omega with the big context, always call a standalone lemma).
- Tail c49->d1b: the skeleton splits on `xc49rcx % 64 = 0` (x86 shift count masking). Generate TWO segment lemmas by adding the hypothesis `xc49rcx = 0` (case A) resp. `1 ≤ xc49rcx ∧ xc49rcx < 64` (case B) and passing `Nat.mod_eq_of_lt` / the hypothesis to the janus64_run simp list so the split disappears; gseg.py currently only parses the first goal.
- The segment bed->c49 (doubling) depends on `(ofNat 64 xbedrcx).msb`: xbedrcx is the signed shift n = 62 - s in [-1, 62] (value (2^64-1) for n = -1); the doubled words are produced exactly when n = -1.
- Remember: never `ps | grep` with a pattern matching your own command line followed by kill (it killed my shell twice).
