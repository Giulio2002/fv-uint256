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

## FV-I3 session (2026-11-06 pm) -- fd chunk loop
* Commits on fv/wi: 3ad53c0 (fd loop WIP), 0e29fd7 (SfdTopSpec). FV-J + main informed; FV-J waits for `extCfg` (an SfdCfg built from Extracted.dataAddr/contractAddr) which I must define when the proof closes.
* SfdTopSpec.lean (Extracted-free): SfdCfg record, TopPre/TopPost/SfdSummary; window bound lo+4800 provisional.
* Done and compiling (lean/Fv256/): SfdFdMath (accV, chunk lemmas, firstBad lemmas, chunk_allDec_iff/decSum), SfdFdLem (tab_word, z_store0..3, add4 = 4-limb adc chain => (X+Y)%2^256).
* Amd64/SfdFdLoop.lean: FdInv (loop-head invariant), fd_next (round bookkeeping: FdInv i -> FdInv (i+1), proved), fd_round (WIP):
  pw call (pw_sum) OK; ParseUint-ok branch: i=0 path complete up to fd_next application (sorry-free trace fine); Mul path: call mul_sum via ReachesRet.call (needs `until [Fv256.Amd64.SfdMul.mulEntry]`, ret addr 4933898 written at s4-152), post facts hz4/hp4/hx*/hy3 transferred to S4 through frames; janus64_run to fd+0x1ab (after adds), then to fd+0x1c4 (jle), then branches at fd+0x1da / fd+0x1c6 (hbr : (Int cast) nS-19i <= 19 or its negation) -- all compile.
  STILL TODO in fd_round: (1) tail run to `head` per branch then `refine reach_name; intro S2 hS2; refine fd_next ...` (copy from the i=0 block; hval from `add4` with x=S.mem limbs (hXs/mval), y=S4 limbs (hYs/hp4); hFm = frame chain hFa/hFb + 4 writes at z); (2) pw-error branch (`janus64_run [hz3c] until [fd + 0x1e5]`, TeObj via TeObj.congr_src, not started); (3) fd_loop induction (strongRecOn on 5-i) + FdInv init from FdPre (copy table with tab_word, zero z, 3 stores) + exit: i=5 / rem<=0 -> ok result (fromDec_ok_of_none) and the remaining=0 early exit; empty string -> eof.
* PITFALLS: (a) `janus64_run ... until [head]` after the adds OOM'd at 60G (lp31/lp32): do NOT `exfalso; omega` on many branches with huge goals; stop at the branch pcs and decide with the visible hbr. (b) whole fd_round needs maxHeartbeats 64M; one 20-60 min compile per edit: COORDINATOR ORDER: split into segment modules (~20-35 insns each, gseg/gen_segment.py + SegCompose.seg_trans, see fv/wb7 NOTES-B7.md), each <5 min/<20G. Suggested cut points: A = loop head -> call pw (stores of i, W, rem), B = pw return -> call Mul, C = Mul return -> add -> head. Keep fd_next as is. (c) literal unification: state helper lemmas with explicit address equalities (z_store3 takes `a2 = zz+16`), never rely on `s4-88+16 =?= s4-72`. (d) hS3F-style MemFrame with two small ranges (not one coarse range) so readLE facts survive. (e) tools: build/run.sh NAME MODULE (MEM=.. env), build/lk.sh; results in build/out/NAME (ENDMARK). Kill by exact pid (lake pid under heavy-run/timeout).

## FV-I5 session (2026-11-06/07) -- fromDecimal amd64 CLOSED, top level started
* fd_sum (fromDecimal amd64 Summary, takes the six runtime contracts hif hnew hmg hmv hwb1 hwb2, NO sorry) is DONE: chain of small files
  Amd64/SfdFdHd (FdInv, fd_next), SfdFdPro (fd_pro), SfdFdEof, SfdFdRnd (PwCtx, fd_to_pw, fd_to_pw_small), SfdFdMid (fd_ret_to_mid, fd_err_ret, MidInv),
  SfdFdPost (fd_post_call), SfdFdA (M2Inv, fd_mid0), SfdFdB (fd_to_mul, fd_add), SfdFdC (fd_midK), SfdFdD (fd_incr), SfdFdE (fd_round), SfdFdF (fd_nil), SfdFdG (fd_loop, fd_sum).
  Each builds in ~15-60 s. Old monolith SfdFdLoop.lean removed (copy in scratch only).
* extCfg: Amd64/SfdTopCfg.lean (commit 4dae8a8). Amd64/SfdTopBr.lean: defeq bridges (env_to/env_of/mod_to/mult_to/chunk_to/teobj_of) between SfdTopSpec(extCfg) and Extracted-level defs.
* Dev loop: `build/run.sh NAME Fv256.Amd64.Module` (HEAVY_PRIORITY=0, MEM 30G); output build/out/NAME; probe with `janus64_run [...] until [..]; all_goals trace_state; all_goals sorry`.
  heavy-run admission needs 60 GB free on / (disk was at 55 GB: deleted own stage/ jcache/).
* Recipes learnt: `until [abbrevAddr]` with an abbrev like `fd + 0x117` does NOT auto-apply ReachesRet.done: use `refine reach_name ?_; intro S2 hS2; refine ReachesRet.done (by rw [hS2]; first|rfl|decide|simp [m,fd]) ?_`
  (reach_name is in SfdToError); for a literal segAddr abbrev (pw, mulE) done is automatic. `X.trans (Y.mono (by ... omega)) (by ...)` with unknown ws makes omega fail: give the mono'd frame an explicit `have` type.
  Branch conditions printed by the stepper: TESTQ BX,BX/JNE -> `(S'.regs 3).toNat = 0`; CMP/JLE -> zf/sf of `(2^64 - 19*i + nS) % 2^64` and `(nS - ofNat (19*i)).msb`; provide those facts (hsf : msb = false, hzf : ... ≠ 0).
  Use `refine name_state (P := fun S1 => ...) ?_; intro S1 hS1` (Rnd) to name the concrete final state when the goal is already the post.
* TOP LEVEL (SetFromDecimal, sfd=0x4b4620) design:  fromDecimal call at sfd+0xad; frame 64 bytes (push BP; sub 0x38); spills: sp0+16 = pS (0x50), sp0+8 = z (0x48), sp0-36 = len1 (0x28), sp0-28 = base1 (0x30).
  Points: L0 = sfd+0xe0 (zero-skip loop head: DX=j, SI=j-1, CX=len1, BX=base1), X0 = sfd+0x12a (after loop, DX=i), B0 = sfd+0x57 (len compare: BX=pS+sp, CX=n-sp). 
  Plus skip uses a mask: base1 = pS + (if len1>0 then 1 else 0) (SARQ trick) -- pointer only equals pS+plusEnd when the remainder is non-empty (irrelevant when length 0).
  Zero loop: decoderune_sum (SfdDecode, verified) used when byte>=0x80: rune>=128 so never '0'. Characterise i by startPos_spec/startPos_lead + uniqueness (no zerosFrom induction needed).
  Then CMPQ CX,78: <78 -> fromDecimal; ==78 -> runtime.cmpstring vs maxStr (.rodata#575028b4) then JLE -> fromDecimal else ErrBig256Range; >78 -> ErrBig256Range. Need a shift lemma fromDec b n p = fromDec (fun k => b (p+k)) (n-p) 0 (and syntax lo shift) -- NOT YET WRITTEN.
  Probe file Amd64/SfdTop1.lean (probe1, with sorry) shows the 6 first-stage paths.

## FV-I5 update (2026-11-07): TOP LEVEL front half DONE; Mod fix; remaining = back half
* Mod FIXED (bd5cf1e): old Mod+Env was contradictory on amd64 too (SfdModTest.lean regression; `mod_contra_old` in SfdWitMod.lean). New Mod excludes (T,T+48) from Outside-priv; Sat.modEnv_sat (SfdWitMod.lean, Extracted-free) proves new Mod+Env satisfiable. nS=0 guards in TopPre/FdPre.
* Top-level files (Amd64/): SfdTopA (TopSt, PostA, top_pro: entry+'+' skip to sfd+0x3a), SfdTopB (TopMid/LoopInv/TailInv defs, top_b0/b1/b2, top_tail), SfdTopC (top_ls, top_lb, top_lend, top_ld [decoderune call via ReachesRet.call decoderune_sum]),
  SfdTopD (top_loop induction, top_front: entry -> B0 = sfd+0x57 with TopMid). ALL SORRY-FREE and building (each < 2 min).
  Math: Fv256/SfdTopMath.lean + DecCongr.lean copied from fv/wb7 (startPos_a/b/nz/end, fromDec_shift, decParse_lt/eq/gt78/big, dec_of_fd, shiftRes).
* sfd addresses: fromDecimal call at sfd+0xcd (0x4b46cd) from the ==78 path and sfd+0xcc ... ; call sites: <78: sfd+0xcc (0x4b46ec `CALL fromDecimal` -> ret sfd+0xd1 =0x4b46f1: ADDQ $0x38,SP; POPQ BP; RET);
  ==78: sfd+0x5f spills, cmpstring call sfd+0x80 (0x4b46a0), JLE sfd+0x88->sfd+0x9e reload AX/BX/CX from 0x48/0x30/0x28(SP) then CALL fd (0x4b46cd), epilogue 0x4b46d2; >78 / cmpstring>0: ErrBig256Range loaded from errBig (+8), ADDQ 0x38,SP; POPQ BP; RET.
  Spill slots (SP1 = sp0-64): 0x28(SP1)=sp0-24 (len1), 0x30(SP1)=sp0-16 (base1), 0x20(SP1)=sp0-32 (zero-loop DX spill), 0x48(SP1)=sp0+8 (z), 0x50(SP1)=sp0+16 (pS).
* REMAINING (back half), port arm64 /srv/fv-uint256-wB7/lean/Fv256/Arm64/SfdTopC.lean+D.lean (fdpre_of, call_post, top_c1/c2/c3a/c3_gt/c3_le, top_fin, top_err, sfd_sum):
  fd window for the call: [lo, sp0-40) (rsp_fd = sp0-72; fd needs lo+4432 <= rsp_fd, rsp_fd+32 <= hi'); FdPre from TopMid via Env.shrink/Env.frame0; ChunkAll via chunkAll_hi/chunkAll_frame (copy);
  results map FdPost -> TopPost with dec_of_fd + TeObj.congr_src; cmpstring: CmpstringContract64 (Janus.Contracts.CmpstringAmd64) on maxStr; hfin from lexGt_iff (SpecI) for n'=78.
  Then: SfdSummary theorem (extCfg) = sfd_sum taking the six runtime contracts + CmpstringContract64; then Extracted-level correctness + Witness (nonvacuous) + janus verify on 77fb30cc.

## FV-I5 update 2 (2026-11-07): top level back half mostly done
* DONE (sorry-free, building): SfdTopE (fdpre_of, CallSt, callSt_of, FdCtx, c1_post, top_c1 = <78 digits to the fd call), SfdTopF (top_epi, top_fin: fd result -> TopPost, all 3 cases eof/ok/syntax), SfdTopG (top_range [ErrBig exit at sfd+0xb8 or sfd+0x8a], top_c2 [>78], CmpCtx, c3a_post, top_c3a [==78: spills + cmpstring call, RA 4933285 = sfd+0x85]).
* Specs changed meanwhile (all committed, last 281a0b4 + later): SfdCfg plain tuple def, Res abbrev (SpecI from fv/master), accessible guard (nS=0 ∨ accessible), Mod fix.
* REMAINING for sfd_sum: (1) cmp_after (S'' after CmpstringContract64 return: TopSt via a topSt_of_callSt lemma [CallSt has regs 4 = sp0-72; S'' has sp0-64], AX = BitVec.ofInt 64 (strCmp Sc.mem (pS+sp) maxStr 78 78) [cmpResult64]) , (2) cmp_val (strCmp = 1 <-> lexGt: UtilI.strCmp_eq_one_iff + TopMath.lexGt_congr2; Janus strCmp_cases for ∈{-1,0,1}), (3) top_c3_gt (AX=1: JLE not taken -> pc sfd+0x8a -> top_range with TopMath.decParse_gt78), (4) top_c3_le (reload AX/BX/CX from sp0+8/sp0-16/sp0-24 [0x48/0x30/0x28(SP1)], CALL fd with ret 4933330 [sfd+0xd2]; use fdpre_of with hfin from lexGt_iff + decSum_maxDigit (copy arm64 SfdTopC top_c3_le), FdCtx ret=4933330, then top_fin with decParse_eq), (5) sfd_sum: seg_trans top_front, by_cases lt/gt/eq 78 as arm64 SfdTopD.sfd_sum; call fd via ReachesRet.call (fd_sum impl R R2 T b L lo (sp0-40) z (Sc.regs 3) (Sc.regs 1) hif hnew hmg hmv hwb1 hwb2) hpc hpreFd, and cmpstring via ReachesRet.call hcmp (CmpstringContract64 (link impl) cmpAddr 16).
* THEN: Amd64/SetFromDecimal.lean (Extracted-level `correctness` + `Witness.nonvacuous`, see arm64 /srv/fv-uint256-wB7/lean/Fv256/Arm64/SetFromDecimal.lean + SfdWitA/B/C for the witness recipe; amd64 contracts are over `Extracted.program.link impl`, not ofImpl), then `janus verify` on 77fb30cc: lakefile rev, `lake update janus`, binary /srv/janus-fvA-pin77f/bin/janus, JANUS_CACHE_DIR=/srv/janus-ops/jcache-shared, no --keep-workspace.

## FV-I5 update 3 (witness complete, verify V2 launched)
- correctness is over `Extracted.program.link impl` (ImplApart Extracted.program impl is unsatisfiable: extraction segments contain stub addresses), with `hcmp` (CmpstringContract64).
- Witness: SfdWitA (stub runtime: newobject/mallocgc/memmove/wb1/wb2 via janus64_live_*, after `rw [linked_eq]`), SfdWitB (ifaceeq model + cmpstring byte loop, literal 4204160), SfdWitC (concrete "7" state, Mod/Env/MultOK/ChunkAll/pre0, hret, setup), `Witness.nonvacuous` in SetFromDecimal.lean. All compile (lake build, Janus 655a23fa, rc=0), no sorry.
- Real verify: `build/vfy2.sh V2 Fv256/Amd64/SetFromDecimal.lean <correctness> <Witness.nonvacuous>` on pin 77fb30cc, log build/logs/V2.log.

## HSfd-amd64: client-facing statement of the SetFromDecimal library lemma (PLANNED, proof pending; FV-I5 2026-11-07)
Module `Fv256.Amd64.SfdLib` (Extracted-free; library program `Fv256.Amd64.SfdProg.program`, entry `SfdProg.sfd`), clients import it plus `Fv256.Amd64.SfdTopSpec`.
```
theorem Fv256.Amd64.SfdLib.hsfd_of_link
    (E : Janus.Amd64.Program) (impl : List Janus.Amd64.Segment) (cfg : SfdCfg)
    (hlink : <E contains the library's segments/stubs, same exit>)   -- discharged by `decide` on the client's Extracted.program (bit-reproducible harness)
    (R : RtInv) (R2 : IfaceModel) (T : Nat)
    (hif : Ifaceeq (E.link impl) (E.contractAddr "runtime.ifaceeq") R2)
    (hnew/hmg/hmv/hwb1/hwb2/hcmp : the six contracts over (E.link impl), exactly as in `SetFromDecimal.correctness`) :
    ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (E.link impl) SfdProg.sfd R R2 T b' L' lo' hi' z pS' nS'
```
i.e. exactly the `hsfd` hypothesis shape J2's UnmarshalText already uses (`SfdSummary cfg (link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS'`, `sfdEntry = SfdProg.sfd = 0x4b4620`), with `cfg = extCfg` (SfdTopCfg). Pre = `TopPre cfg ...` (contains `RetOK`, that is internal to Summary; the top-level Ensures uses `TopPre0`). Post = `TopPost cfg ...`. No other change to specs.

## FV-I5 update 4 (n10 status, 2026-11-07 evening) -- HANDOVER
- Target moved to n10 51d592da: lean/lakefile.toml + lake-manifest.json pin /srv/janus-fvA-pin51d @ 51d592da (`lake update janus` done); build/ex-amd64-SetFromDecimal regenerated with n10 `janus extract` (old one kept as build/ex-amd64-SetFromDecimal.77f; command: extract harness-amd64 <sym> --max-functions 64 --contract {cmpstring,ifaceeq,mallocgc,memmove,newobject,gcWriteBarrier1,2,3,memclrNoHeapPointers}).
- Top-level Ensures pre is `TopPre0` (no RetOK; `retok_of` derives it from RetAddr+CallSetup+window) for the n10 RetLow audit; SfdSummary keeps TopPre. NOT yet checked with the n10 auditor on the statement itself (the verify never reaches the audit stage).
- `janus verify` (77f V2-V7, n10 N4/N5/N6; shared cache, fresh cache, JANUS_LAKE_JOB_MEM=16G) all END with only "SfdTopI.olean does not exist" after 4000-5000 s; own/lib has oleans only up to SfdTeBody/SfdTePre (nothing from SfdTeSum0 on). Hand compile of the whole chain with plain `lean` against the kept n10 workspace (build/m51/run.py, log build/m51/log) is ALL rc=0 incl. Fv256.Amd64.SetFromDecimal (both theorems elaborate). Peak RSS: SfdTeSum0 5.2 GB/241 s, SfdTeSum1 16.0 GB/596 s, everything else <=3 GB. Evidence sent to main for U-SILENT-DEP.
- NEXT: (1) split SfdTeSum1 (te_body's final `all_goals` obj/F block, SfdTeBody.lean) and SfdTeSum0 below ~8 GB (Hid wrappers/ continuation lemmas), rerun `JC=/srv/janus-ops/jcache-n10 JB=/srv/janus-fvA-pin51d/bin/janus KW=--keep-workspace JJ=1 build/vfy2.sh N7 Fv256/Amd64/SetFromDecimal.lean <correctness> <Witness.nonvacuous>` (NO --keep-workspace for the final); (2) then SfdProg/SfdLib/SfdLink library (planned statement above), then Scan disch_sfd on fv/wsc.

## FV-I7 update 5 (2026-11-07 evening) -- LIBRARY DELIVERED
- Chain ported off `Extracted`: all Amd64/Sfd* (except SfdWit*) import `Fv256.Amd64.SfdProg` (generated by tools/gen_sfdprog_amd64.py: 8 segments, 5 stubs, 11 contracts, dataAddr consts; cross-checked on 4 extractions). Extraction REDONE with the canonical SFD contract flags (cmpstring ifaceeq mallocgc memmove newobject gcWB1/2/3 growslice slicebytetostring concatstring2): 5 stubs, so `LinkEq.LibIn` (needs E.stubs == lib stubs) holds for Scan ex3 and J6 n10 extractions. Old extractions: build/ex-amd64-SetFromDecimal.n10a/.77f. identity.json binary must be "../harness-amd64".
- `Fv256.Amd64.SfdLib.hsfd_of_link` (planned statement, hE : LibIn, hca : ContractsAgree) + `SfdLink.hLib_of_decide/hca_of_decide`; `Fv256/LinkEq.lean` identical to fv/wsc. Method: contracts over E.link impl -> ProgEq -> SfdProg.program.link (rest ++ impl) -> sfd_sum -> back. Axioms clean. Commit 73467f9.
- SetFromDecimal.lean (Extracted-level) now: hLib, hca by decide; correctness = ensures_of_summary64 (hsfd_of_link ...).
- Hand build: build/m52/go.sh MODULE LOG (out in build/m52/out). Timings (lib, unsplit): TeSum0 291 s/5.1 GB, TeSum1 570 s/16 GB, rest <=1 min each.
- TODO: split TeSum0/1; janus verify N8 (build/vfy2.sh N8 ...; JC=jcache-n10); multi-limb witness (needs memmoveUptoSeg64 + toy R ok for chunks 1..19); Scan disch_sfd.

## FV-I5 update 5 -- finding from FV-SD (a4aba0ce4360bd913), for the successor
- The "SfdTopI.olean does not exist" error is a masked symptom. FV-SD patched janus to print the real error: janus's own compile of SfdTeSum0 (inside its bwrap sandbox) ran ~964 s at up to 18 GB, then failed with 8x "Tactic `assumption` failed" at SfdTeSum0.lean:26:2 (the te_body macro), some "Unknown identifier hS6q'". janus then silently fell back to Lake, which OOMs in the 24 GiB scope.
- The identical `lean` command unsandboxed: rc 0, ~280 s, 5.2 GB (my build/m51/run.py uses plain lean, so it reports rc=0 for a module janus rejects). Under `bwrap --unshare-all --die-with-parent --new-session --ro-bind / / --dev /dev --proc /proc --tmpfs /tmp --bind W W --chdir W`: rc 1. Cause not found.
- Suspect: SfdTeBody.lean ~lines 227-235, `try (obtain ... := (by with_reducible assumption : ...))` blocks swallow a failing assumption, so later hS6q'/assumption calls fail. FV-SD's advice: make those `try` blocks hard failures to expose the first failing step; to test any split, compile under the bwrap command above, not plain lean. Do NOT use --unsafe-no-sandbox.

## FV-I7 update 6 (2026-11-07 15:35) -- HANDOVER
- DONE: amd64 SetFromDecimal verified on n10 51d592da, warm 165 s (build/logs/N12.log, includes the multi-limb witness: 45-digit string, chunks 19+19+7, memmoveUptoSeg64 stub, toy R serving chunk sizes 1..19); cold run 1204 s (N11). Scan amd64 verified on fv/wsc (logs/sc5/v5.log). fv/master has both (FV-A2).
- Root causes fixed: debug host-file IO in te_walk (sandbox EROFS swallowed); audit rejects non-ASCII names and Program.contractAddr on non-Extracted programs in the statement -> SfdProg.cfg* literal aliases used by SfdTopCfg.extCfg.
- Error-input witnesses: not added (Witness.nonvacuous only needs the hypotheses satisfiable; error paths are covered by the correctness theorem's TopPost cases).
- NOT DONE: TeSum0/TeSum1 splits (lib modules, 291 s/5.1 GB and 570 s/16 GB, maxHeartbeats 16M); they are cached after the first build per cache. Profile: tactic execution ~226 s of 262 s in TeSum0, spread over many small steps; te_body = macro in SfdTeBody.lean (stages: ifaceeq call, mallocgc->memmove, newobject, final te_post_intro conjuncts).
- Merge of fv/master 3683787 (IO lint) into fv/wi: not done.
