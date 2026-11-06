# NOTES-I (FV-I, then FV-I2: SetFromDecimal amd64)

Branch fv/wi (worktree /srv/fv-uint256-wi). Janus pin 655a23fa (`/srv/janus-wi-pin3/bin/janus`, lean/lakefile.toml, lake-manifest.json,
build/vfy.sh uses it + /srv/janus-ops/jcache-shared). Dev workspace: build/ws (package override -> build/kept/janus, a COPY of a kept
janus-verify workspace so cache GC cannot delete it; if "package directory not found" re-run `build/vfy.sh rpN build/ex-amd64-SetFromDecimal
Fv256/Amd64/SfdDecode.lean Fv256.Amd64.SfdDecode.decoderune_sum`, copy the printed "Kept workspace" janus/ dir to build/kept/janus).
Dev run: `DEPS="Fv256.SpecI Fv256.UtilI Fv256.HexLemmas Fv256.SumC64 Fv256.Amd64.SfdEnv Fv256.Amd64.SfdTePre Fv256.Amd64.SfdTeLem" HEAVY=1 MEM=30G build/devbg.sh REL.lean OUT.out`
(copy a changed SfdTePre/SfdTeLem into build/ws and `lake build` them first). Scratch variants of the te_sum0/te_sum1 file with timing marks: build/scratch/ScrTe{0,1}.lean
(copy into lean/Fv256/Amd64/ to use; delete again). Marks/debug output: build/out/marks.txt (file build/out/debug_flags enables FLAG/FRAME dumps in te_flags).

## Verified (janus verify): decoderune_sum, pu_sum, mul_sum. Compiles: pw_sum (hte still a hypothesis).
## strconv.toError, ErrSyntax case (lean/Fv256/Amd64/SfdToErrorX.lean, SfdTePre.lean, SfdTeLem.lean)
* te_sum = summary_split (te_sum0 [wbFlag read = 0]) (te_sum1 [wbFlag read /= 0]); both use the macro `te_body` (hygiene off).
* te_sum0 COMPILES (lake env lean, 655a23fa): 281 s total, ~4.6 GB; per stage: prefix ~4 min, flags 5-25 s, F (te_base) <1 s, c5-c8 ~55 s, c9-c10 ~25 s, c11/c12 ~15 s.
* What made it fast: (1) te_base (SfdTeLem) proves the base MemFrame as an extraction-free lemma (was 10.6 min / +11 GB inside te_frame);
  (2) te_flags closes the infeasible flag branches by rewriting the two flag reads to `s.mem.readLE 6156064 4` (needs `Apart wbFlag` unfolded: hAwb) and `absurd`;
  (3) te_omega/te_atom = janus_clear_irrel before omega, cheap alternatives first; (4) te_copy/te_src/te_hfr (SfdTeLem) for the copied-bytes conjunct;
  (5) NEVER `contradiction`/`simp_all`/`simp ... at *` in these contexts (371-488 s per call).
* te_grab (SfdTePre) names the mallocgc postcondition facts by content (replaces rename_i; the 655a23fa repin had broken the positional names).
* te_sum1 (write-barrier branch) OPEN. After te_flags exactly one goal remains. Its memory chain: newobject -> w16; wb call 1 (window [(r4-96-4096, r4-96)])
  -> w9; stores into t/buffer slot (w13 = wb slot pointer) ; wb call 2 -> w2; then final stores. LiveFrames over `L ++ [q] ++ [t]`, MemFrames over `R.rt ++ [window]`.
  Needed: (a) a te_base variant `te_base1` with the two extra wb MemFrames and `InRanges slot 8 R.rt` for the buffer-slot stores (F case; the 6 stores at t need
  `exact f_i`, the slot stores need the wb contract's slot-in-rt fact); (b) field reads through the wb LiveFrames (readLE_nil rule, `InRanges (t+k) 8 (L++[q]++[t])`)
  plus `Apart t 48 slot 16` (state it as Apart; check what WbLiveContract64 gives for the slot); (c) te_inv/te_copy for that shape.
  Print the main goal with `trace_state` at "all_goals refine te_post_intro" (use build/scratch/ScrTe1.lean).
## Remaining chain after te_sum: drop hte from pw_sum -> fromDecimal chunk loop (mul_sum) -> prefix/cmpstring -> witness -> first full janus verify of SetFromDecimal amd64.
## Rules learnt: no pkill -f/pgrep -f in the same shell (kills your own shell); heavy queue waits are 15-25 min; marks go to build/out/marks.txt (stderr is buffered by lake).

## FV-I2 session log (2026-11-06)
* te_sum1 (write-barrier branch) restructured with extraction-free lemmas in SfdTeLem.lean (all compile in seconds):
  te_base1 (F case: newobject frame + wb2 + stores + wb1), te_f0..te_f5 (field reads through the two barrier LiveFrames),
  te_copy1 (copied bytes), inv_slot1/outside_of_apart3 (invariant after a store into a barrier slot), win_a/win_k (window apartness
  without omega). Generic helpers (inRanges_fields, frame_writeLE_rt, ...) moved from SfdTePre to SfdTeLem; SfdTePre imports SfdTeLem.
* LESSON: `omega` on goals about q/t in this context is catastrophic (c11 hung >10 min): pass explicit disjunction facts
  (hS6t', hS2t', hA3, hWt, win_a hAw hlow ..) instead of `(by te_omega)`. `clear * - h` is Mathlib, not available.
* LESSON: te_sum1 needs set_option maxHeartbeats 64000000 (16M was exhausted by the prefix alone; the symptom is a `whnf` timeout
  at the last case).
* Dev loop for te_sum1 alone: the generator in this log: take SfdToErrorX.lean, keep te_body macro + te_sum1, add `te_mark` elab
  (appends to build/out/marks.txt) -> lean/Fv256/Amd64/ScrTe1.lean (delete it before any janus verify!). Run via
  `DEPS="Fv256.SpecI" HEAVY=1 MEM=30G TMO=3000 build/devbg.sh Fv256/Amd64/ScrTe1.lean qN.out` after copying SfdTePre/SfdTeLem into build/ws and
  `lake build Fv256.Amd64.SfdTePre` there. Under load: prefix ~10 min, whole run 16-30 min.
* SfdPw.lean: hte replaced by the six contract hypotheses (hif hnew hmg hmv hwb1 hwb2); `have hte := te_sum ...` inside. NOT yet compiled.
* Next: fd loop (SfdFd): head = fromDecimal+0xa0 (0x4b4840), regs DX=i CX=remaining SI=len(bs) BX=ptr, stack: z @0x98(SP), bs.ptr @0xa0(SP),
  multipliers copy @0x60(SP); per iteration pw_sum (ParseUint) then (i>0) Mul(base,base,mult_i) + inline 4-limb add; z_i = decSum b lo_i (n-lo_i),
  step = decSum_split; no-overflow from FdPre's last conjunct. Then SetFromDecimal top (prefix '+', zero-skip loop with decoderune (rune >= 128 so
  never '0'), len compare, runtime.cmpstring contract (CmpstringContract64) against twoPow256Sub1, call fromDecimal).

## FV-I2 update (14:30): speed fix
* ROOT CAUSE of the 10-min toError prefix: `te_grab` used `isDefEq` on memory terms (355 s). Now syntactic `==` -> `lake build Fv256.Amd64.SfdPw` (TeSum0 || TeSum1, X, Pw) = 632 s wall under load ~40 (was 1414 s); TeSum1 compiles at maxHeartbeats 16M.
  Profile recipe that found it: `set_option profiler true in set_option profiler.threshold 4000 in` on a scratch copy cut right after the suspected stage (`all_goals sorry`).
* Remaining per-stage costs (under load): run3 (memmove+newobject) was NOT slow itself; obj cases c5-c10 ~50 s each (the `hM := rfl` unification against the State record); the all_goals prelude (assumption searches) was 424 s before switching to `with_reducible assumption`.
* build/bld.sh OUT MODULE... runs `lake build` of the dev workspace under heavy-run.
* FV-J (a3d85265d747eebd7) agreed the SetFromDecimal summary shape (ok / eof / range with z unchanged / syntax via TeObj); SfdTopSpec (Extracted-free Pre/Post) must be created when the top-level statement is final; dataAddr parametrisation of the library summary is an OPEN question for main/FV-A.
* TODO order: (1) optionally cut obj cases c5-c10 further (use `show` instead of rfl); (2) fd chunk loop; (3) SetFromDecimal top; (4) witness; (5) first verify; (6) arm64 (nothing started).
