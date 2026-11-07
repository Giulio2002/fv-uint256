# NOTES-B7 (FV-B7, arm64 SetFromDecimal: fromDecimal loop + top level) -- worktree /srv/fv-uint256-wB7, branch fv/wb7 (off fv/wi4 75df2ff)

Split agreed with FV-I4 (a6fa3045cf5aa5e10): FV-I4 keeps te_sum0/te_sum1/te_sum/pw_sum (Arm64/SfdPw.lean, PwSum hypothesis);
I own NEW files Arm64/SfdFd*.lean (fromDecimal loop), Arm64/SfdTop*.lean (SetFromDecimal top, then Extracted correctness + witness).
Build: lean/ lakefile pinned to /srv/janus-fvA-pin655 @655a23fa; build with ../build_lb.sh <Module> (lake build, log build/lb-<Module>.log, ENDMARK).

## Done
- lean/Fv256/SfdFdMath.lean, SfdFdLem.lean: copied verbatim from /srv/fv-uint256-wi (FV-I2, ISA independent; untracked there; identical content merges).
- Arm64/SfdFdSpec.lean: FdPre/FdPost/FdSum statement (arm64 analogue of amd64 SfdFd): mulTab = 0x1b6540 (multipliers),
  ioEOF = 0x1b5c10, frame 160 bytes, window lo+4440 <= SP, SP+32 <= hi, GuardOK s 32.

## arm64 fromDecimal facts (fd = 0xb8b50; go tool objdump of harness-arm64; listing in `go tool objdump -s 'uint256.\(\*Int\).fromDecimal$'`)
- entry: stack check (16(R28) vs SP-32), frame 160 (pre-index store of x30 at SP-160, x29 at SP-8 rel. new SP...), spill pS to 176(SP'), zero z (2 STP), CBZ nS -> EOF path (0xb8bc0: LDP io.EOF -> R0,R1, ret).
- else: z -> 168(SP'), pS -> 176(SP'), copy multipliers (40 bytes at 0x1b6540) to 112..152(SP'); R3 = i = 0, R4 = len = nS; JMP head.
- HEAD = fd + 0x9c (0xb8bec): R0 = z, R1 = pS, R2 = remaining (signed, nS-19i), R3 = i, R4 = len(bs) (= R2 whenever R2 > 0), exit by
  CMP $5,R3 BGE -> return nil (0xb8d40), CMP $0,R2 BLE -> return nil (0xb8d2c).
- round: spill i->56, mult[i]->104, len->64, rem->48 (all SP'-relative). rem>19: bounds check rem<=len, ParseUint(pS+rem-19, 19, 10, 64); else ParseUint(pS, len,..).
  After: CBNZ R1 (err itab) -> return (R0,R1)=(R1,R2) of ParseUint (0xb8d18). i==0: store (num,0,0,0) to z; else tmp Int at 72(SP') = {num,0,0,0}, Mul(tmp,tmp,mult[i]) (R0=R1=tmp, R2=W),
  then z += *R0 (ADDS/ADCS x4 at 0xb8ca4..0xb8cec), then loop increment at 0xb8bd8 (R3 = i+1, R2 = rem-19), chop bs (bounds check len >= rem-19 at 0xb8d04, BCS back).
- SetFromDecimal (sfd = 0xb89b0): '+' skip, zero-skip loop with runtime.decoderune for bytes >= 0x80 (at 0xb8ab8..), len compare vs 78 with runtime.cmpstring against the
  digits of 2^256-1 (rodata at ADRP+2315), error return LDP from 0x1b5bc0-ish, then call fromDecimal (0xb8a70 / 0xb8a98).

## TODO (in order)
1. compile SfdFdSpec (lake build Fv256.Arm64.SfdFdSpec), commit.
2. FdInv at HEAD, fd_next / fd_round (call PwSum via ReachesRet.call, Mul via mul_sum, inline add, bounds checks), prologue, exits; amd64 SfdFdLoop.lean (FV-I2) is the template but is itself unfinished (ends in `trace_state; sorry`).
3. SfdTop: plus skip, zero loop (decoderune_sum), cmpstring contract, call fd_sum; Extracted correctness + Witness.nonvacuous; ONE verify.

## Update: fd_pro DONE (Arm64/SfdFdPro.lean, compiles, sorry-free apart from FV-I4's SfdPw)
- FdInv (arm64 loop-head invariant at head = fd+0x9c) defined there; fd_pro: entry (nS != 0) -> head with FdInv 0 (janus_run until [head] + 20-way refine; ~55 s).
- Tricks: abbrev constants (mulTab) must be restated as numeric literals for omega/janus_run (have hmA : 1795392+40 <= lo ∨ ... := hmA0).
- NEXT: nS = 0 (EOF) exit lemma; round (i<5, 19*i<nS): spills, ParseUint call via PwSum (ReachesRet.call), error exit (0xb8d18), i=0 SetUint64 store, i>0 Mul call (mul_sum: tmp at sp'+72, W = mult[i] at sp'+104 spill) + 4-limb ADDS/ADCS into z, then loop increment+chop (0xb8bd8..0xb8d14) back to head with FdInv (i+1); exits 0xb8d2c/0xb8d40 (return nil when rem<=0 or i>=5).

## Update 2: fd_eof (Arm64/SfdFdEof.lean) and fd_to_pw (Arm64/SfdFdRnd.lean) DONE, sorry-free
- fd_eof: nS = 0 exit -> FdPost (eof disjunct).
- fd_to_pw: from FdInv i (i<5, 19i<nS, rem>19) run to the ParseUint call, PwPre discharged (window lo'=s.sp-4440, hi'=s.sp-112, Env.frame0+Env.shrink, ChunkOK.mono_win).
- Interface: PwSum fits; FV-I4 added `s'.mem.readLE (s.sp-8) 8 = s.mem.readLE (s.sp-8) 8 ∧ s'.mem.readLE s.sp 8 = ...` to PwPost (preserves saved FP/LR of the caller). Rebase SfdPw when FV-I4 sends the hash.
- NEXT: rem<=19 variant of fd_to_pw (second call site returns at 0xb8c5c; same pw), ReachesRet.call pw (hpw lo' hi' p len), error exit (0xb8d18, TeObj.congr_src), MID = fd+0x114 state, then i=0 store / Mul call+add / increment+chop to head (i+1), exits, fd_loop induction, fd_sum.

## Update 3: fd_sum CLOSED (Arm64/SfdFdF.lean), takes hpw : forall lo' hi' p len, PwSum impl R R2 T b L lo' hi' p len
Chain of files (all sorry-free, each < 1 min): SfdFdSpec (FdPre/FdPost/FdSum), SfdFdPro (FdInv, fd_pro), SfdFdEof (fd_eof), SfdFdRnd (PwCtx, fd_to_pw, fd_to_pw_small),
SfdFdMid (fd_ret_to_mid, fd_err_ret), SfdFdInc (M2Inv, fd_incr, Env.congr), SfdFdA (MidInv, fd_mid0), SfdFdB (fd_to_mul, fd_add), SfdFdC (fd_midK),
SfdFdD (fd_post_call), SfdFdE (fd_round), SfdFdF (fd_nil, fd_loop, fd_sum).
Lessons: never `omega` in contexts holding many hypotheses or after `.trans`/`.mono` without explicit intermediate `have` types (hangs 20+ min); use `exact` with structured Outside conjunctions and small standalone lemmas (out_sub, win_sub, toInt_small, toInt_nonpos).
To derive hpw: PwSum from pw_sum (FV-I4) + the six runtime contracts (pw_sum ... hif hnew hmg hmv hwb1 hwb2).
TODO: SfdTop (plus skip, zero-skip + decoderune, cmpstring, call fd_sum), Extracted-level correctness + witness, ONE verify.

## Update 4 (end of this session): SfdTopSpec committed; Keep threaded through the fd proof
- Arm64/SfdTopSpec.lean: arm64 port of FV-I3's SfdTopSpec (TopPre/TopPost/SfdSummary; TopPost preserves [sp-8, sp+8)). FdPost now has `Keep s s'` (same words), FdInv/MidInv/M2Inv carry it; whole fd chain rebuilt clean.
- GAP FOUND (both ISAs): TopPre has no fact about the bytes of the 78-digit rodata string that SetFromDecimal compares against with runtime.cmpstring
  (arm64: ADRP+ADD $2315 at 0xb8a34, i.e. page 0xb8000+0x3c000... recompute from `go tool objdump`), nor accessibility/disjointness of it. A library-level (Extracted-free) proof needs
  `SfdCfg.maxStr`, `∀ k<78, m.readLE (maxStr+k) 1 = maxDigit k`, `accessible maxStr 78 false`, `Outside maxStr 78 [(lo,hi),(z..)]` in TopPre (discharged from the extraction's data at the Extracted level).
  cmpstring: Janus.Contracts.Cmpstring.CmpstringContract (hypothesis, like pw's contracts); UtilI.strCmp_eq_one_iff gives lexGt.
- SfdTop proof plan (not started): entry+stack check+spill (frame 80, FP at sp-8, z at sp+8, pS at sp+16); '+' skip (CMPW 43, SUB, NEG/ASR63/AND1, ADD); zero loop (decoderune_sum for bytes >= 0x80, mask trick via
  UtilI.mask_keep, i = first non-'0' byte or last index); branches CMP $78; cmpstring call (contract) then fd_sum call (hpw) at 0xb8a70/0xb8a98; error returns load from ErrBig256Range (0x1b5bc0-ish) and io.EOF via fd.
  Result must match decParse (startPos/plusEnd/zerosFrom in SpecI); fromDecimal's FdPost gives fromDec b n p; TopPost wants decParse.
- Then Extracted-level correctness + Witness (lib_summary / codeIn_of_sub, cfg from the extraction), discharge hpw from pw_sum, ONE verify on 77fb30cc.
HEAVY_PRIORITY=0 for janus verify (noted)

## Update 5: SfdTop start
- arm64 maxStr (78-digit rodata string of 2^256-1) = 0xf490b (ADRP at 0xb8a34: page 0xb8000 + 0x3c000, + 2315).
- Arm64/SfdTopPro.lean: probe of the entry up to ta = 0xb89f0 (after plus skip) for nS = 0 runs; needs LITERAL pc (0xb89b0 / 0xb89f0, not segAddr abbrevs), g+24 <= 2^48 and `Nat.mod_eq_of_lt` for g+16, sp%16.
  The nS != 0 case (byte load, '+' compare, plus skip) is the next step; then zero loop at 0xb8aa8 with decoderune (call at 0xb8adc), cmp 78 / cmpstring (0xb8a40) / fromDecimal calls (0xb8a70, 0xb8a98), error returns.
- HEAVY_PRIORITY=0 for the final janus verify (coordinator request).

# HANDOVER (FV-B7 -> next worker), written at the end of session
State: branch fv/wb7, worktree /srv/fv-uint256-wB7, HEAD = see `git log -1` (4ee796e or later). Build: `./build_lb.sh Fv256.Arm64.<Module>` (lake build, log build/lb-<Module>.log, ENDMARK line; janus pin 655a23fa
via lean/lakefile.toml -> /srv/janus-fvA-pin655; for the final verify use 77fb30cc + workaround per coordinator). HEAVY_PRIORITY=0 for heavy-run.

DONE (all sorry-free except FV-I4's pw_sum body in Arm64/SfdPw.lean): fd_sum : FdSum impl R R2 T b L lo hi z pS nS from hpw (Arm64/SfdFdF.lean + SfdFdSpec/Pro/Eof/Rnd/Mid/Inc/A/B/C/D/E).
 FdPost has `Keep s s'` (words at s.sp-8, s.sp preserved). SfdTopSpec.lean (TopPre/TopPost/SfdSummary, SfdCfg with maxStr; commit 2e2ff749) is the target statement.
 SfdTopPro.lean: probe `top_pro_probe` (entry -> pc 0xb89f0, only nS=0 branch runs; the rest `all_goals sorry`).

NEXT LEMMA (exact): Arm64/SfdTopPro.lean `top_pro` for nS != 0: from entry pc 0xb89b0 to pc 0xb89f0 (call it `ta`).
 Code: 0xb89b0 ldr x16,[x28,#16]; cmp sp; bls morestack; 0xb89bc MOVD.W x30,-80(sp); 0xb89c0 str x29,-8(sp); 0xb89c4 sub x29,sp,#8; 0xb89c8 str x1,96(sp) [topSP+16 := pS];
  0xb89cc cbz x2 -> 0xb89f0; 0xb89d0 ldrb w4,[x1]; cmpw #43; bne -> 0xb89f0; 0xb89dc sub x2,x2,#1; neg x4,x2; asr x4,x4,#63; and x4,x4,#1; add x1,x1,x4; 0xb89f0 str x0,88(sp) [topSP+8 := z]; cbz x2 -> 0xb8a18.
 Needed hypotheses (see probe): LITERAL pc 0xb89b0, g+24<=2^48 (Env e6), g+16 < 2^64 via Nat.mod_eq_of_lt, sp%16=0, accessible (sp-88) 120 true, accessible pS nS false, byte read s.mem.readLE pS 1 (case split b=43 vs not).
 Post to prove (state at 0xb89f0): sp = s.sp-80, x29 = s.sp-88, x28/x18 same, R0=z, R1 = pS + plusEnd, R2 = nS - plusEnd (plusEnd b n in SpecI: 1 if n>0 and b 0 = 43), mem = writes at s.sp-80(LR), s.sp-88(FP), s.sp+16(pS), s.sp+8(z) over s.mem.
NEXT: (1) zero-skip loop head 0xb8aa8 (CMP R2,R3; ldrb; cmpw #127; bgt -> decoderune call at 0xb8adc with R0=p,R1=len,R2=idx; cmpw #48; beq loop; after loop s=s[i:] via mask trick `AND R4->63 ... (R3-R2)>>63` = UtilI.mask_keep) -- use SfdDecode.decoderune_sum (DecPre/DecPost) for bytes >= 0x80 (result rune >= 0x80 != '0');
 invariant relates to SpecI zerosFrom/startPos (startPos_spec, startPos_lead); (2) length compare 0xb8a18: CMP $78,R2: BLT -> fromDecimal call 0xb8a98; BNE (>78) -> ErrBig256Range return (LDP from 0x1b5bc0+? at 0xb8a4c/0xb8a80);
 ==78 -> spill, runtime.cmpstring(R0=p,R1=len,R2=maxStr(0xf490b),R3=78) at 0xb8a40 via Janus.Contracts.Cmpstring.CmpstringContract (hypothesis), then R0>0 -> ErrBig return else fromDecimal call at 0xb8a70 (reload z,p,len from slots 88/64/56(RSP));
 fromDecimal call: ReachesRet.call (fd_sum impl R R2 T b L lo hi z p len hpw) -- window = same [lo,hi) (FdPre needs lo+4440 <= sp-80, i.e. lo+4520 <= s.sp; Env etc. re-establish at the call state; ChunkAll/MultOK/io.EOF facts from TopPre). Epilogue 0xb8a74: ldur x29,-8(sp); ldr x30,80(sp)!; ret (reload from topSP-88 / topSP-80 slots; FdPost.Keep protects them). Result: map fromDec results to decParse (decParse b n = fromDec b n (startPos b n) or .range; lexGt via UtilI.strCmp_eq_one_iff).
 (3) discharge: TopPost eof/ok/range/syntax cases (syntax: TeObj from FdPost, p = pS+startPos+lo').
 (4) Extracted level: Arm64/SetFromDecimal.lean like Arm64/Reciprocal.lean (Summary.of_codeIn + codeIn_of_sub for SfdProg.program, cfg from extraction: maxStr=0xf490b, ioEOF=0x1b5c10, errBig=?, mulTab=0x1b6540 etc. from `go tool objdump` / extraction data), Witness.nonvacuous (EqHashModel witness, RtInv/IfaceModel instances: see how FV-I4's pw witness plans), hpw from FV-I4's pw_sum + six contracts.
 (5) ONE verify: HEAVY_PRIORITY=0 heavy-run, janus 77fb30cc (+ fv_carry_simp_v1 only matters for amd64), --theorem ...correctness --theorem ...Witness.nonvacuous.
LESSONS: never omega in big contexts or inside inline .trans/.mono (give explicit `have` types); structure Outside facts with `exact ⟨..⟩`; use literal pcs; numeric abbrev constants must be re-stated as literals for omega/janus_run; `case` names for refine goals; fresh `have`s after refine apply only to the first goal.

# HANDOVER 2 (FV-B8 -> next worker): top level DONE, remaining = Extracted level + Witness + hpw + verify
State: branch fv/wb7, worktree /srv/fv-uint256-wB7, HEAD = `git log -1` (SfdTopSpec doc commit after d3ac4b2).
DONE (all sorry-free, each file < 40 s with `lake env lean`): Fv256/SfdTopMath.lean, Fv256/DecCongr.lean (copy of wJ's), Arm64/SfdTopA.lean (cfg, TopSt, top_pro),
 SfdTopB.lean (PostA/TopMid/LoopInv/..., b0/b1/b2, loop ls/hop/lb/lend/ld1/ld2/tail, top_loop, top_to_mid), SfdTopC.lean (fdpre_of, call_post, top_c1/c2/c3a, top_epi,
 top_fin, top_err, top_range, cmp_after, cmp_val, top_c3_gt, top_c3_le), SfdTopD.lean: 
 `Fv256.Arm64.SfdTop.sfd_sum (impl R R2 T b L lo hi z pS nS) (hpw : ∀ lo' hi' p len, SfdPw.PwSum impl R R2 T b L lo' hi' p len)
   (hcmp : CmpstringContract (SfdProg.program.link impl) 0x11cc0 16) : SfdSummary cfg (SfdProg.program.link impl) 0xb89b0 R R2 T b L lo hi z pS nS`
 axioms: propext, Classical.choice, Quot.sound only. `cfg` (SfdTopA) holds the binary addresses (maxStr 0xf490b, errBig 0x1b5b60, ioEOF 0x1b5c10, mulTab 0x1b6540, numErrType 0xdc840,
 numErrItab 0xf6940, errItab 0xf6920, synConst 0xf5940, strconvErrSyntax 0x1b5eb0, wbFlag 0x1e34c0, fnStr 0xeb483, contract addrs via SfdProg.program.contractAddr).
Spec changes vs 2e2ff749: only TopSpec.Mod gained `8 ≤ R2.depth` (documented; Janus Iface.lean:84). fd window trick: fromDecimal is called with window [lo, s.sp-48) so caller's FP/LR words survive.
Decoderune: SfdDecode.DecPost narrowed to [(sp-24,sp-8),(sp+8,sp+16)] (callee never touches the caller FP slot; matches arm64 calleeStack convention).
Build: `HEAVY_PRIORITY=0 /srv/janus-ops/bin/heavy-run -- ../build_lb.sh Fv256.Arm64.SfdTopD`; fast iteration: `cd lean; lake env lean Fv256/Arm64/SfdTopX.lean` (needs olean of imports -> lake build once).
Janus pin for the lake build is still 655a23fa (lakefile); the final verify must use /srv/janus-fvA-pin77f/bin/janus (77fb30cc) — repin lakefile (`lake update janus`) first or rely on Lake-free verify.

REMAINING (not started):
1. Extracted level (Arm64/SetFromDecimal.lean, `namespace Fv256.Arm64.SetFromDecimal`): extract `build/harness-arm64` 'github.com/holiman/uint256.(*Int).SetFromDecimal' with `--contract` for runtime.cmpstring (+ the existing contract set used by FV-I4's extraction: mallocgc, memmove, newobject, gcWriteBarrier1/2, ifaceeq); build Extracted.program; show SfdProg.program's segments embed (codeIn_of_sub / lib_summary, template Arm64/CodeIn.lean, ModSum.lean, DivModLib.lean) and transfer sfd_sum; `correctness : Ensures Extracted.program Extracted.entry [z,pS,nS,…] pre post` with pre = TopPre cfg … (cfg instantiated from Extracted.dataAddr/contractAddr; prove equal to `cfg` by decide/rfl), post = TopPost; runtime hyps: the six contracts of pw_sum + hcmp + whatever Iface contract pw_sum needs.
2. hpw: from FV-I4's `SfdPw.pw_sum impl R R2 T b L lo hi p len hif hnew hmg hmv hwb1 hwb2` (still `sorry` in my tree; coordinate with a6fa3045cf5aa5e10 / branch fv/wi4; rebase SfdPw when sorry-free). `fun _ _ _ _ => pw_sum ...`.
3. Witness (`SetFromDecimal.Witness.nonvacuous`): a concrete model for R (toyR, see Arm64/IntoBig.lean Witness: newobjectSeg/wbSeg/LiveSat), R2 (IfaceModel witness for ifaceeq; see Janus Contracts IfaceSat), CmpstringSat for hcmp, and a concrete State satisfying TopPre cfg (memory from Extracted.data: errItab/T descriptors for StaticOK, multipliers table + 10^(19k) objects for MultOK, ioEOF/errBig/maxStr rodata, ChunkAll contracts for every chunk, z, string). Biggest remaining piece; FV-I4's pw witness needs the same Mod/Env/StaticOK parts -> share.
4. ONE janus verify: HEAVY_PRIORITY=0, /srv/janus-fvA-pin77f/bin/janus, --theorem …correctness --theorem …Witness.nonvacuous, no --keep-workspace.

# HANDOVER 3 (FV-B9): Extracted level + Witness DONE; remaining = pw_sum (FV-I4) + the single verify
State: fv/wb7 @ 3d7bea5+ (merged fv/master pin 77fb30cc, merged fv/wi4 57bbfc8; lakefile -> /srv/janus-fvA-pin77f).
DONE: Arm64/SfdLink.lean (generic CodeIn lemmas), SfdCfgE.lean (cfgE from Extracted.dataAddr/contractAddr), SetFromDecimal.lean
 (`correctness` over Extracted.program.link impl, runtime contracts over Extracted.program.ofImpl impl + ImplApart, sfd_sum transferred; `Witness.nonvacuous`),
 SfdWitA/B/C.lean (stub runtime implA at contract addresses, R0 ifaceeq, cmpstring loop, concrete state, pre0, nonvacuous_core), SfdWitReg.lean (mod_contra_old regression).
 Spec fixes: Mod was UNSATISFIABLE (T descriptor inside R2.priv vs Outside priv) -> hT law, T range excluded; TopPre/FdPre pS window conjuncts guarded by nS=0.
 SfdProg regenerated (stubs = extraction's; the old stub set made ImplApart false via osyield); tools/gen_sfdprog.sh and scripts/contract-flags.sh carry the flag set
 (cmpstring ifaceeq mallocgc memmove newobject wb1 wb2 wb3 growslice slicebytetostring concatstring2).
Fast iteration (no lake for Extracted modules): scratch-b9/{chk.sh,mk.sh,linkall.sh} + scratch-b9/lib (Extracted.olean compiled by hand; relink after lake rebuilds). Untracked scratch.
Only sorryAx in `correctness` = FV-I4's pw_sum (Arm64/SfdPw.lean). When sorry-free: merge fv/wi4, replace nothing else (hpw is already `pw_sum` applied to the converted contracts in SetFromDecimal.lean).
FINAL: build/verify1.sh (HEAVY_PRIORITY=0 heavy-run, pin77f janus, shared jcache, both theorems, no --keep-workspace); a trial run was queued at the time of writing (build/verify1.log).
HANDOVER 3 addendum (da2b5f8): trial `janus verify` (build/verify1.sh, 3m26 warm with shared jcache) => Witness.nonvacuous VERIFIED; correctness fails ONLY the axiom audit (sorryAx from SfdPw.pw_sum, FV-I4).
 Audit lessons: no consumer inductive/structure reachable from a statement (SfdCfg -> plain def 16-tuple; Fv256.I.Res -> abbrev triple with match_pattern defs).
 TopPre/FdPre carry nS=0 guards on: pS window facts (2), accessible pS nS. Mod has hT.
 TO FINISH: when FV-I4's pw_sum is sorry-free: `git merge fv/wi4`, rebuild (lake build Fv256.Arm64.SfdTopD; scratch-b9/mk.sh for Extracted modules), then run build/verify1.sh via heavy-run (HEAVY_PRIORITY=0) and record the time.
