# NOTES-I (FV-I, SetFromDecimal amd64) — state at hand-off

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
