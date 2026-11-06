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
