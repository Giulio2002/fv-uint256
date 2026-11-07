# (*uint256.Int).Scan -- FV-N, branch fv/wsc (worktree /srv/fv-uint256-wsc), 2026-11-07

## Done
* Source (master 48f3f44, conversion.go:805-850) read; spec = lean/Fv256/SpecScan.lean (`ScanSpec.sciParse`, Extracted-free, builds with `lake build Fv256.SpecScan` on rev 77fb30cc).
* Extraction (janus-wr-pin2 binary, harness-{amd64,arm64} copied from fv/wfn): build/ex-{amd64,arm64}-Scan, flags = FV-J's build/ctflags
  (`--contract` runtime.cmpstring ifaceeq mallocgc memmove newobject gcWriteBarrier1/2/3 memclrNoHeapPointers) + `--contract runtime.slicebytetostring`.
  amd64 42 fns / 14501 B, arm64 42 fns / 13952 B. Scan 261/288 B, scanScientificFromString 549/496 B (code, same extraction), IndexByteString 24+297 (indexbytebody) / 224,
  SetFromDecimal 377/416, Exp 857/688, MulOverflow 165/176. GtUint64 is inlined (`cmpq $0x4d`; `or` of the upper limbs).
* lean/Fv256/IndexByteSpec.lean (e2055b1): the hibs library-summary statement for FV-S (both ISAs).

## Code facts (amd64 offsets from Scan 0x4b3ac0; arm64 Scan 0xb8050)
Scan(dst=RAX, typeword=RBX, data=RCX): nil type -> Clear dst (two 16-byte stores of X15), return 0,0. Else hash word `[type+16]` is compared (string 0xf88732b8,
[]byte 0x7efbbf65) then the type pointer (type:string 0x4c6b00, type:[]uint8 0x4c5460; arm64 same shape). string: ptr,len = `[data]`,`[data+8]`, call
scanSci. []byte: `slicebytetostring(&tmp[0x18(rsp)], ptr, len)` (stack temp, contract) then scanSci. else `newobject(errors.errorString)` {ptr "unsupported type", 16}, itab
`go:itab.*errors.errorString,error`.
scanSci(dst, ptr, len): frame 0x68(+8). len==0: Clear. IndexByteString.abi0 (args at (rsp),8(rsp),0x10(rsp), result 0x18(rsp); caller reloads R14 and X15 after).
idx==-1: tail `SetFromDecimal(dst,s)`. else `idx<=len` bounds check (panicBounds unreachable), SetFromDecimal(dst, s[:idx]) -> error returned as is; `len-idx == 2 && s[idx+1]=='0'` -> nil;
exp Int local at rsp+0x48 (zeroed), SetFromDecimal(&exp, s[idx+1:]); `exp[0] > 77 || exp[1]|exp[2]|exp[3] != 0` -> ErrBig256Range (loaded from the global);
base Int {10,0,0,0} local at rsp+0x28; Exp(&exp, &base, &exp); MulOverflow(dst, dst, &exp) (overflow flag in BL) -> ErrBig256Range or nil.
arm64: same, `cbnz`/`cmn x0,#1` forms, IndexByteString in registers (x0 ptr, x1 len, x2 byte).

## Proof plan (two levels, each conditional on summaries; none is started beyond the spec)
Level A: `scanSci` summary over (link impl) at the scanSci entry: Pre = SetFromDecimal's `TopPre` (Fv256.{Amd64,Arm64}.SfdTopSpec, FV-I) with the window shrunk by the
frame (lo + 4800 + 0x80 <= rsp), Post = `sciParse` cases, as TopPost (value in val256 dst on ok; error words as in FromDecimal; MemFrame [R.rt ++ R2.priv ++ (lo,hi) ++ dst]).
 Hypotheses: hsfd (as FV-J's FromDecimal: `∀ b' L' lo' hi' z pS' nS', SfdSummary cfg (link impl) sfdEntry ...`), hibs (IbsLibA/IbsLib64 at the IndexByteString entry),
 hexp (Exp over ExpProg: `exp_summary` + lib_summary, Amd64/Arm64 ExpSum), hmo (MulOverflow: NO library program yet; generate one with tools/gen_libprog*.py like MulModProg and
 prove `Ensures.toSummaryIn`, or take it as hypothesis first), newobject/mallocgc/memmove/ifaceeq/wb live contracts for the SFD closure.
 Segments: (1) prefix to IndexByte call; (2) idx=-1 tail SFD; (3) idx found: SFD(s[:idx]) call, error branch / "0" branch; (4) second SFD call on the local exp
 (TopPre re-derived for z=&exp, window [lo, sp-0x68-...), pattern `toppre_of_call` of FromDecimalSpec, MultOK z<->exp); (5) exp>77 branch; (6) Exp call on the locals; (7) MulOverflow call + flag branch.
 Value facts: `Exp` post = 10^e mod 2^256 with e<=77 so 10^e < 2^256; product overflow iff mant*10^e >= 2^256 (MulOverflow flag) -- matches sciParse.
Level B: Scan wrapper: cases src nil / string / []byte / other. Needs `hsci` (the level A summary at scanSci's entry, taken from a library-style transfer or proved in the same file),
 the slicebytetostring live contract (copy the hypothesis form from Dec/Hex wrappers, FV-C/FV-E), newobject contract for errors.New. The []byte case: the copy made by
 slicebytetostring is a fresh string outside L (frame lemma like FV-J's UnmarshalDecJ), bytesAt equality via decParse_congr-style lemma for sciParse (only bytes 0..n-1 read).
 Unsupported type: ret ptr = itab `go:itab.*errors.errorString,error`, data = fresh 16-byte block in R.rt holding ("unsupported type" ptr, 16); dst untouched.
Witnesses: `Scan.Witness.nonvacuous` per ISA covering EVERY hypothesis (build the satisfiability of the Pre early: SFD's Mod/Env have been unsatisfiable before, see FV-B9).
Audit: run a sorry-proof `janus verify` of the statement first (consumer defs only plain defs, no structure/inductive; Res is a tagged triple).
Pin: 77fb30cc (master lakefile); icall line (d52a1656) is NOT needed for Scan (no abstract callee).

## Status update (later 2026-11-07)
* Pulled from fv/wj (byte-identical copies, do not edit): lean/Fv256/Amd64/{SfdTopSpec,SfdEnvC,FromDecimalSpec}.lean (SfdTopSpec = fv/wi b982015).
* lean/Fv256/MulOverflowProg.lean: GENERATED (tools/gen_libprog.py --base Fv256.UmulProg, from ex-amd64-Scan + ex-amd64-MulOverflow; MulOverflow calls umul, so the
  program is UmulProg + the MulOverflow segment). The MulOverflow SUMMARY over it is NOT proved: the existing Amd64/MulOverflow.lean proof is an Ensures over the
  MulOverflow extraction (5 aliasing cases, 295-2679 s); to get `Summary MulOverflowProg.program entry ..` re-target it (copy MoCases/A..E to the library program,
  as ExpProg/ExpSum were) and transfer with `Fv256.CodeIn.lib_summary hcLib`. Exp needs nothing new: `Fv256.Amd64.ExpMain.exp_summary` over ExpProg + lib_summary
  (see Amd64/Exp.lean line ~55 for the CodeIn side condition); its Pre needs 0xa8 bytes below the call SP writable and StackGuardOK s 0x20.
* arm64: nothing generated yet (gen_libprog_arm64.py, Arm64/ExpProg exists, MulOverflow arm64 likewise needs a library program + re-targeted proof).
* DESIGN QUESTIONS for the Scan statement (blocking the audit verdict; not decided):
  1. hsbts: `slicebytetostring` live contract is stated over an RtContract64 with readiness H (F2's FormatFast: `RtContract64 .. ssAddr rt 4096 H (slicebytetostringSpec ..)`),
     while the SFD closure uses the allocator model `RtInv R`. The []byte case needs both in ONE statement; ask the engine owner whether `R.rt`/`R.inv` can serve as `rt` and
     how `H` relates (UnmarshalText/JSON by FV-J2 faces the same question: see wip-j/DecWrappers.draft.md).
  2. Scan's Pre: take `TopPre C R R2 T b L lo hi dst pS nS (viewS s pS nS)` where viewS replaces regs 3/1 by the string pair read from the header at the data word, so the
     string facts are reused verbatim; the type-switch adds (tw = 0) / (tw = type:string, header readable) / (tw = type:[]uint8, slice header readable) / (other tw: hash word
     readable). scanSci's own Pre: TopPre plus `lo + 4800 + 0x80 <= rsp` (frame 0x68 + saved rbp + spills) and the local Int slots rsp+0x28 / rsp+0x48 inside [lo, hi).
  3. amd64 IndexByteString reads `internal/cpu.X86` (HasAVX2, a writable global NOT copied by the extractor): the hibs summary (IndexByteSpec.IbsPreA) must take the
     accessibility of that byte as a parameter (address from Extracted.dataAddr) -- FV-S must add it; arm64 has no such dependency.
* Nothing of the seven segments is proved yet; sorry-proof audit run of the Scan/scanSci statement not done (blocked on 1 and 2).

## Coordination (FV-X, fv/wx in /srv/fv-uint256-wx): amd64 hibs amendment
IbsPreA (avx : Nat) p n c s := accessible avx 1 false = true ∧ (old conjuncts); IbsSummaryA P entry avx p n c; IbsLibA P entry avx. avx = Extracted.dataAddr.«internal/cpu.X86» + 68
(0x5df444 in this harness): only READABILITY assumed, summary covers both HasAVX2 values. Library programs Fv256.IbsProgA.program (entry 0x402bc0) / Fv256.IbsProg64.program (0x11f10).
Hash and lemma names to follow from FV-X; the consumer's hibs must use the amended signature (IndexByteSpec.lean here is superseded on merge).
Decisions (main): slicebytetostring via the LIVE contract (RtLiveContract64 .. slicebytetostringLive) over the SAME allocator model R as SFD (copy FV-J2: fv/wj
Amd64/UnmarshalDec.lean `dec_call_pre`, `SbPost`; SbtsFacts.lean `loc`); pin the consumer to u14 head 72b96825. Pre = plain conjunction def (like PreU) with an early satisfiability lemma.
MulOverflow: library programs + retargeted cases generated (Amd64|Arm64/MoLib/{A..E,Top}.lean, mo_summary); builds queued: build/mo.sh (amd64) then build/mo64.sh.

## MulOverflow library summaries: DONE both ISAs (lake build, axioms propext/choice/Quot.sound, no sorry)
Fv256.Amd64.MoLib.mo_summary (over Fv256.MulOverflowProg.program, entry 0x4b7360) and Fv256.Arm64.MoLib.mo_summary (over Fv256.Arm64.MulOverflowProg.program, entry 0xbadb0).
Pre = `∃ ret, RetAddr .. ∧ CallSetup (program.withExit ret) entry [z,x,y] s ∧ <MulOverflow Ensures pre>`, Post = `ABIReturn s s' ∧ <Ensures post>`. Transfer with Fv256.CodeIn.lib_summary (CodeIn proof as in Amd64/Exp.lean).
Case proofs are mechanical sed-retargets of MoCases (not janus verify runs).

## hibs amd64 taken from FV-X (fv/wx 3ce79d4): lean/Fv256/{IndexByteSpec,IbsProgA,IbsProg64,IbsMath,IbsA,IbsAWit}.lean + tools/gen_libprog*.py (--no-stubs). Not rebuilt here.
`Fv256.IndexByte.ibs_lib_A : IbsLibA Fv256.IbsProgA.program 0x402bc0 0x5df444`; consumer passes avx := Extracted.dataAddr.«internal/cpu.X86» + 68 (= 0x5df444, rfl/decide).
IbsPreA also needs `s.mem.accessible (s.regs 4).toNat 32 false = true` (caller frame [RSP,RSP+32) readable: args just stored there). Segments "internal/bytealg.IndexByteString.abi0", "indexbytebody"; transfer via codeIn64_of_sub / lib_summary.
arm64 hibs: pending from FV-X.
arm64 hibs taken from FV-X (fv/wx cc91d5d): lean/Fv256/{IbsA64,IbsSynd,IbsAlign,IbsVec64,IbsA64Wit,IbsMath}.lean. `Fv256.IndexByte.ibs_lib_64 : IbsLib64 Fv256.IbsProg64.program 0x11f10`
(segment "internal/bytealg.IndexByteString", base 0x11f10, 224 B); IbsPre64 unchanged (X0,X1,X2, admissible X30, PageReadable). Not rebuilt here.

# HANDOVER (FV-N, 2026-11-07, context large) -- read this first
Worktree /srv/fv-uint256-wsc, branch fv/wsc, HEAD = commit adding this section (previous 9709227). Never push; identity Giulio2002, trailer Co-Authored-By: Claude Sonnet 5.5.
## Available (all committed here, lake-built or taken from owners)
SpecScan.sciParse; MulOverflow library summaries (Amd64/Arm64 MoLib.mo_summary, built); hibs both ISAs (taken from fv/wx 3ce79d4 / cc91d5d, NOT rebuilt here: run `lake build Fv256.IbsA Fv256.IbsA64` first);
SFD spec copies (Amd64/{SfdTopSpec,SfdEnvC,FromDecimalSpec}); Exp via ExpMain.exp_summary + lib_summary; extractions build/ex-{amd64,arm64}-Scan; env: `cd lean && lake update janus` done (rev 77fb30cc).
## NOT started (needs the u14 pin first)
Main decided: consumer on u14 head 72b96825 (live slicebytetostring contract `RtLiveContract64 .. (slicebytetostringSpec ..) slicebytetostringLive` over the SAME allocator R as SFD).
So: (1) `git -C /srv/janus worktree add /srv/janus-wsc-pin 72b96825`, build bin/janus, set lakefile rev to it, `lake update janus` (COLD Janus rebuild ~ an hour; shared jcache /srv/janus-ops/jcache-shared);
(2) copy FV-J2's pattern from fv/wj: Amd64/UnmarshalDec.lean (`SbPost`, `dec_call_pre`, PreU), SbtsFacts.lean (`loc`), UnmarshalText.lean (the []byte->string->SFD call shape: slicebytetostring with a stack temp buf, then SFD with budget b - roundupsize n, L ++ [fresh string]).
## Statement shape (amd64; FV-X mirrors it for arm64)
`theorem correctness (impl) (R : RtInv) (R2 : IfaceModel) (T b) (L) (lo hi) (dst tw dw : BitVec 64) (hif hnew hmg hmv hwb1 hwb2 : live contracts as FromDecimal) (hsbts : RtLiveContract64 .. slicebytetostringLive)
 (hsfd : ∀ b' L' lo' hi' z pS' nS', SfdSummary cfg (link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS') (hibs : IbsLibA (link impl) ibsEntry (Extracted.dataAddr.«internal/cpu.X86»+68) ...)
 : Ensures (link impl) Extracted.entry [dst, tw, dw] (ScanPre ..) (ScanPost ..)`
ScanPre (plain conjunction def): the core of TopPre for z := dst (RetOK, Mod, Env, `lo + 4800 + 0x80 ≤ rsp` (scanSci frame) + Scan frame, MultOK dst, ioEOF/errBig/maxStr facts, Buffer dst 32 true, dst apart from window/R.rt..)
 ∧ caller frame [RSP,RSP+32) readable (IbsPreA) ∧ typeswitch cases: tw = 0 ∨ (tw = type:string ∧ header(dw) readable ∧ StringPre pS nS = TopPre's pS/nS conjuncts with pS,nS read from the header)
 ∨ (tw = type:[]uint8 ∧ slice header readable ∧ same string facts ∧ slicebytetostring preconditions incl. budget) ∨ (tw ∉ {0,string,[]uint8} ∧ [tw+16] readable). Use `viewS s pS nS := {s with regs := setRegF (setRegF s.regs 3 pS) 1 nS}` to reuse TopPre verbatim.
ScanPost: by cases: nil -> val256 dst = 0, error words 0,0; string/[]byte -> `sciParse (bytesAt s.mem pS) nS` as in FromDecimal's post (ok v: val256 dst = v, regs 0=0,regs 3=0; eof/range: io.EOF / ErrBig256Range words; syntax lo len: itab numErrItab + TeObj with chunk (pS+lo, len));
 other -> regs 0 = itab `go:itab.*errors.errorString,error`, regs 3 = fresh 16-byte block in R.rt holding (ptr to "unsupported type", 16), val256 dst unchanged; MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo,hi),(dst,dst+32)]).
Then: sorry-proof `janus verify` for the audit verdict (build a satisfiability lemma `∃ s, ScanPre ..` early: SFD's Mod/Env were unsatisfiable once, FV-B9), then the seven segments (see "Proof plan").
Level A order: (2) idx=-1 tail (single SFD tail call) first, then len==0, then the e-branch (two SFD calls; toppre_of_call pattern with z=&exp local), exp>77, Exp call (lib_summary of ExpMain.exp_summary; needs 0xa8 below SP writable + StackGuardOK s 0x20), MulOverflow (mo_summary, window 152+16 below SP).

# HANDOVER 2 (FV-SC, 2026-11-07) -- read after HANDOVER 1
## State (branch fv/wsc, pin integ/n10 51d592da, lakefile rev set, `lake update janus` done; janus binary bin/janus-n10b)
* STATEMENT DONE + AUDIT PASSES (sorry-body verify reaches the axiom stage only): lean/Fv256/Amd64/{ScanCfg,ScanSpec,Scan}.lean.
  - Audit rules learned: no RetOK in pre (use FV-I5's TopPre0, copied SfdTopSpec from fv/wi 095ad29; FromDecimalSpec adapted: `unfold TopPre TopPre0`);
    hsfd/hibs CANNOT be theorem premises (audit: "constrains a runtime variable of a contract hypothesis") -> they are lemma hypotheses in the segment
    lemmas and must be discharged in the FINAL theorem via CodeIn/lib_summary (sfd_sum of fv/wi needs hif hnew hmg hmv hwb1 hwb2 hcmp; ibs_lib_A; mo_summary; exp_summary).
  - Final theorem premises now: hif hnew hmg hmv hwb1 hwb2 hsb hcmp (contracts only). ScanPre is minimal per case (nil / string / []byte via PreB (no okH) / other).
  - SciPre/SciPost (scanSci entry summary) are defined in ScanSpec. ScanStrPost covers ok/eof/range/syntax via sciParse.
* Level A segment 1 DONE: lean/Fv256/Amd64/ScanA0.lean `sci_len0` (empty string -> Clear, return nil), compiles in the kept workspace, no sorry.
  Recipe that worked: obtain the TopPre0 fields (pattern in SfdTopA), `janus64_run [hn0, hacc]` (needs the dst accessibility fact as `s.mem.accessible (s.regs 0).toNat 32 true`),
  then post by `refine ⟨kept, Or.inl ⟨0, sciParse by simp [sciParse, hn], regs, val256 via readLE_add 16+16 + readLE_writeLE_*, MemFrame chain with MemFrame.of_writeLE/.writeLE (r := ...)⟩, mf⟩`.
* Kept workspace for iteration: /srv/janus-ops/jcache-shared/v1/consumer/ebc1e099d077a51003799cba/4990d1e65f32e7397ff3fe47/root (`lake env lean Scr1.lean`, 5 s); gc may remove it: recreate with `bin/janus-n10b verify ... --keep-workspace` (logs/sc/v2.sh).
## FINDINGS needed for the next segments
1. After the IndexByteString call the code does `mov %fs:-8, %r14`: the ibs summary does NOT promise R14, so SciPre (and ScanPre) need a TLS fact:
   `s.mem.accessible (s.fsBase.toNat - 8) 8 false = true ∧ s.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat` (+ fsBase kept by Kept). X15 is re-zeroed by xorps. ADD to SciPre/ScanPre (all cases that call IndexByte) and re-run the audit; tell the arm64 worker (arm64 has no such dependency).
2. Next segment: prefix to the ibs call (entry pc `sci+0x4e` = IndexByteString.abi0 call at 0x4b3c2e): `janus64_run until [ibsEntry]` then `Reaches.call (Summary.withExit (hibs p n 101) hret) ?_ ?_ ?_` (pattern: UnmarshalText.lean br_a in fv/wj with sfd; the callee-precondition goal is IbsPreA avx p n c at the call state: [RSP,RSP+32) readable (frame), p/n/c stored at (rsp),8(rsp),0x10(rsp), result slot 0x18(rsp) writable, PageReadable from SciPre).
   Post at pc sci+0x53 (instruction after the call): idx = readLE (sp-0x70+0x18) 8 = indexOfNat (bytesOf s.mem p) n 101, MemFrame s.mem S.mem [(lo,hi)], spills dst/p/n at sp-0x70+0x78/0x80/0x88.
3. Tail calls to SFD need a `toppre_sub` lemma (adapt FromDecimalSpec.toppre_of_call: no new z, window shrinks to [lo, sp3+32) with sp3 = sp1 - 0x78, string = sub-range (p', n') of the original, z = dst or the local Int `exp` at sp1-0x70+0x48 which lies ABOVE the shrunk window: hi3 <= z). ChunkAll for subranges via chunkOK_mono.
4. Witness: SfdWitA/B/C copied to scratch/scw (ScanWitA/B/C, namespace Fv256.Amd64.Scan.Wit, sbts stub added to implA, string page region widened). NOT compiled yet. Needs: real Extracted data in the witness memory for DataLoaded (user decision: no assumed rodata facts), toy interface model whose T/itab words equal the real ones, `janus64_live_memmove_upto N hok` (merged in n10) for an 'e' string (n>=2), ScanWitD for the Scan-level state (hdr at 0x302000, tw = type:string 0x4c6b00, avx 0x5df444 readable).
5. Remaining Level A segments: (2) ibs-prefix [next], (3) idx=-1 tail SFD, (4) SFD(s[:idx]) + "0" branch, (5) second SFD on local exp + >77 branch, (6) Exp call (exp_summary + lib_summary; needs 0xa8 below call SP writable, StackGuardOK s 0x20), (7) MulOverflow call (mo_summary) + flag branch. Then Level B (type switch; slicebytetostring live; newobject for unsupported type), then discharge hsfd/hibs/mo/exp via CodeIn in the final theorem, witnesses, one-run verify.

## Progress after HANDOVER 2 (FV-SC)
* IbsPostA (amd64) strengthened with `s'.fsBase = s.fsBase ∧ s'.df = s.df`; ibs_lib_A / IbsAWit rebuilt (lake build Fv256.IbsA Fv256.IbsAWit OK). hibs for Scan = `Fv256.IndexByte.IbsLibA ...` as is.
* TlsG s (Janus GoABI) is a conjunct of ScanPre (string, []byte cases) and SciPre; audit re-passed (n10 51d592da).
* Level A segment 2 DONE: ScanA1.lean `sci_ibs` (prologue + arg stores + IndexByteString call via hibs, ends at sci+0x53 with `ScanIbsCall.PostK`), helpers in ScanIbsCall.lean (Extracted-free: callMem, pre_of_bv, cont, PostK). All no sorry; checked in the kept workspace only (not yet a full janus verify).
* `sci` abbrev moved to ScanCfg.
* NEXT: segment 3 = from sci+0x53: xorps xmm15; mov fs:-8,r14 (use TlsG.load_reentry with S.fsBase kept; TlsSlotKept from MemFrame + slot apart from the result slot), cmp rcx,-1 (idx = indexOfNat..; -1 <-> find? = none <-> idxE b n = none), je -> tail call SFD(dst,p,n) with `toppre_sub` (TopPre for the SFD call at sp-0x78: NOT YET WRITTEN; adapt FromDecimalSpec.toppre_of_call, z = dst, same string; window shrinks to [lo, sp1-0x58)). Then segments 4-7 as listed above.

# HANDOVER 3 (FV-SC2, 2026-11-07) -- read after HANDOVER 2
## Done since HANDOVER 2 (all committed on fv/wsc; checked with `lake env lean` in the scratch workspace work/ws only, no full janus verify yet except the audit run in logs/sc/v3.*)
* ScanSpec: SciPre/ScanPre now carry `(TlsG s ∧ Outside (s.fsBase.toNat - 8) 8 [(lo, hi)])` (needed so the TLS slot survives the ibs frame). Audit re-run on n10 started (logs/sc/v3.log); arm64 worker FV-SA3 told.
* lean/Fv256/Amd64/ScanSfd.lean (Extracted-free, `Hid` opaque wrapper, TopPre0 projections `.env .mod .lo4 .hi32 .pw .pacc .pwin .pz .chunk`):
  `toppre_sub` (TopPre0 at entry -> TopPre0 for a SetFromDecimal call with window [lo,hi3), receiver z' (dst or local), sub-range string),
  `env_sub` (Env for the shrunk window after in-window stores), `call_pre1` (TopPre for SFD(dst,p,n') called from the scanSci frame: hi3 = sp-88, return address pushed),
  `str_same`, `frame_top`, `top_keep` (reads above the SFD window unchanged, z = dst), `top_acc`, `scanStr_top` (TopPost of the call -> ScanStrPost + MemFrame for the whole string; params off/n' for the exponent call, hok/heof/hrange/hsyn bridge sciParse).
* lean/Fv256/Amd64/ScanIdx.lean: indexOf_none/indexOf_some/sciParse_none/idxE_byte.
* ScanA2.lean `sci_none` = segment 3 (idx = -1: xorps, TLS reload of R14 via explicit hfsa/hfsb/hacc/hval hypotheses in terms of S.fsBase, tail SFD call, ret). Segment lemmas take the entry state s, the post-ibs state S and `hK : ScanIbsCall.PostK s S ..`, conclude `ReachesRet (link impl) (retAddrOf s) S (SciPost ..)` (so later segments are used by earlier ones as lemmas; compose back-to-front).
## Recipes learned
* SPEED: hypotheses TopPre0/Env/RetOK left unpacked made every load/store discharge in janus64_run cost ~2 s and blew the 200000 heartbeat budget; `have hT0 : Hid (TopPre0 ..) := hT; clear hT ..`, run, then unwrap (`have hT : TopPre0 .. := hT0`): segment 15 s -> 3 s, default heartbeats.
* janus64_run on `mov r14, fs:[-8]`: give facts in terms of S.fsBase: `(S.fsBase + 18446744073709551608#64).toNat = S.fsBase.toNat - 8`, `8 ≤ S.fsBase.toNat`, accessible/readLE at `S.fsBase.toNat - 8`.
* The branch `cmp rcx,-1; je` is decided by rewriting the readLE of the idx slot to its value (kidx after `rw [hidx]`).
* Name resolution: dot-notation lemmas on TopPre0 must be declared `_root_.Fv256.Amd64.SfdTopSpec.TopPre0.x`.
* Scratch tooling: work/ws (copy of the kept workspace; add `.lake/build` oleans with work/cc.sh Fv256/Amd64/X.lean, quick check `work/run.sh Scr.lean N`).
## Facts for the remaining segments (amd64, sp = scanSci entry RSP; scanSci frame rsp = sp-0x70; calls at rsp = sp-0x78, SFD window hi3 = sp-88)
* Slots: [sp-88] ibs result/idx (0x18(rsp)), [sp-80] idx saved (0x20), [sp-72] base Int (0x28..0x47), [sp-40] exp Int (0x48..0x67), [sp+8] dst, [sp+16] p, [sp+24] n, [sp] ret, [sp-8] rbp. exp/base lie ABOVE hi3.
* Seg4 (idx found, i<n): pc sci+0x6f.. : cmp bounds (not taken), store i at [sp-80], reload dst/p, call SFD(dst,p,i) [reuse call_pre1 with n' = i]; non-ok -> ret with scanStr_top (off=0; sciParse unfolds to decParse b i for non-ok); ok -> continue (invariant: Env for window hi3, MemFrame to s, DataLoaded for Exp, [sp-80]=i, val256 dst = v, via top_acc/top_keep).
* Seg5: nil case n-i=2 && p[i+1]=='0' -> return nil (sciParse ok v); else zero exp (two movups of xmm15=0), SFD(&exp, p+off, n-i-1) with off = i+1 if n-i-1>0 else 0 (z=exp: toppre_sub with hzO etc.; env_sub from the post-call-1 Env; non-ok -> scanStr_top (off = i+1)).
* Seg6: exp>77 test (cmpq $0x4d,[sp-40]; or of limbs) -> ErrBig256Range loaded from the global (range case). Seg7: base={10,0,0,0}, Exp(&exp,&base,&exp) via ExpMain.exp_summary/lib_summary (Pre needs StackGuardOK s 0x20, StackWritable s 0xa8 0x20, DataLoaded; window [sp-288,sp-88)), MulOverflow(dst,dst,&exp) via MoLib.mo_summary: its Pre is `∃ ret, RetAddr prog ret ∧ CallSetup (prog.withExit ret) entry [z,x,y] s ∧ ..` -> choose ret := the literal return address 0x4b3d70, CallSetup.ret needs readLE sp 8 = ret (exitAddr of withExit); flag in BL.
* DataLoaded after an SFD call: needs a lemma (regions equal via ReachesRet.call_regions + MemFrame on writable ranges [(lo,hi3),(dst,dst+32)] disjoint from data by Tactic.disjoint_of_dataLoaded) -- not yet written.
* Final theorem: hsfd/hibs/exp/mo must be discharged in-proof via CodeIn (sfd_sum of fv/wi, ibs_lib_A, ExpMain.exp_summary, MoLib.mo_summary; see Amd64/Exp.lean hcLib pattern). Level B (type switch, slicebytetostring live, newobject) and witnesses NOT started.

# HANDOVER 3b (FV-SC2)
AUDIT VERDICT (n10 51d592da, sorry-body verify, logs/sc/v3.log, after the InitDone + header-Outside + R.rt-writable additions): PASS -- reaches the axiom stage, fails only on sorryAx.
RULE for the successor: every segment lemma must fit the DEFAULT heartbeats (no maxHeartbeats raise; Scr5.lean used 3M only for exploration) -- split segment 5 into separate lemmas (nil return / call / post-call).

## State
STATE: segments 1-4 done (ScanA0 sci_len0, ScanA1 sci_ibs, ScanA2 sci_none, ScanA3 sci_some [uses ScanA4.sci_after1 stub]). ScanA4.lean currently holds `sci_after1` as a SORRY STUB (segment 5 to prove).
* ScanSpec additions this session (audit re-run requested by main, started 08:13; see logs/sc/v3.log; result must be checked): InitDone cfg R2 s.mem in the TLS conjunct (string/[]byte/SciPre) -- needed because a zero error word would make `test rax,rax` fall through; per FV-SA3's arm64 request: `Outside dw.toNat 16/24 [(lo,hi)]` (string/[]byte), `∀ r ∈ R.rt, accessible r true` ([]byte and other-type), `Outside (tw+16) 4 [(lo,hi)]` (other type).
* work/new/ScanSfd2.lean (NOT yet in lean/Fv256/Amd64; copy it there, it compiles in work/ws): `call_pre2` (TopPre for SFD(&exp, p', n') from the S4 state: needs hlo: lo+4920<=sp, Env S4 window hi3, MemFrame s->S4 [(lo,hi),(dst..)], MemFrame S4->S3 [(lo,hi)], z'.toNat = sp-40, ...), `mask_pos/mask_zero/args_pos/args_zero` (bit-trick of `neg;sar 63;and`: p' = p+(i+1), n'=n-(i+1) if i+1<n, else p'=p, n'=0). ScanSfd.lean also got env_sub2, topPost_split, nz_of_nonok, dl_frame, Inv4, ra_lt (these ARE in the repo after the next commit).
* Scratch for segment 5: work/ws/Scr5.lean (`sci_after1` skeleton: by_cases n-i=2 / byte=48; runs need the maximal heartbeats 3000000 temporarily and take 100 s: SPLIT into separate lemmas (nil-return lemma, call lemma, post-call lemma) -- each janus64_run with hidden hyps (Hid) is cheap, the cost is several runs in one declaration). Stepper needs: `hb : S4.mem.readLE (p+(i+1)) 1 = byte`, `hba` accessible, mask equalities `hmk : (0#64 - (n - ofNat(i+1))).sshiftRight 63 &&& ofNat(i+1) = ofNat(i+1)` (from mask_pos), `(p + ofNat (i+1)).toNat = p.toNat+(i+1)`.
* Remaining: seg5 (nil return -> ok v; else second call with call_pre2 + scanStr_top (off:=i+1, hres from sciParse_some_ok: non-ok exponent -> r, syntax -> syntax (i+1+lo))), seg6 (exp>77 -> range; sciParse=range via sciParse_some_ok + 77<e), seg7 (Exp via ExpMain.exp_summary/lib_summary with window [sp-288,sp-88): StackGuardOK s 0x20, StackWritable s 0xa8 0x20, DataLoaded (dl_frame with regions: use ReachesRet.call_regions); MulOverflow via MoLib.mo_summary: pre is ∃ ret, RetAddr .. ∧ CallSetup (prog.withExit ret) ..: choose ret = literal return address, CallSetup.ret: readLE sp 8 = ret since exitAddr of withExit = ret; value facts: exp < 2^256 etc), Level B, final theorem discharge of hsfd/hibs, witnesses, full verify.

# HANDOVER 4 (FV-SC3, 2026-11-07) -- read after HANDOVER 3b
## Done (all committed on fv/wsc, every lemma within DEFAULT heartbeats, NO sorry in ScanA*.lean)
* Level A segments 5, 6, 7 proved; `sci_after1` (ScanA4) is now a dispatcher. Files:
  - ScanA5.lean: `sci_nil` ("0" exponent -> ok mantissa), `sci_post2_ok/_err`, `sci_call2` (second SFD call from S3: pre via ScanSfd2.call_pre2, post split), `sci_pre2_pos/_end/_b` (the three stepper runs to sfdEntry; the mask `neg;sar 63;and` is decided with `hmk` from ScanSfd2.mask_pos/mask_zero).
  - ScanA6.lean: `decParse_zero` (empty text = eof), `sci_tail_eof/range/syn/ok` (sciParse after the 'e' with the tail's decParse), `Inv5` (state after ok exponent call, at sci+0x129), `TopPre0.errAcc/errOut`.
  - ScanA7.lean: `ExpSumm`/`MoSumm` (callee-summary hypotheses, plain defs), `sci_range1` (exp > 77), `sci_exp1`+`sci_expcall` (base Int, Exp call, post -> `Inv6`), `sci_aftexp`+`sci_mocall` (MulOverflow call pre/post -> `Inv7`), `sci_aftmo` (test bl; ok / ErrBig256Range), `sci_after2` dispatcher. ScanSfd2: `top_keep2` (reads above the window apart from receiver z).
  - Callee hypotheses are threaded `hsfd hexp hmo` through sci_after1 / sci_some (A3). `hibs` only in sci_ibs (A1). NOT yet written: the Level-A glue `sci_summary` (sci entry: len0 / ibs / none / some dispatch), Level B, final theorem, witnesses.
## BLOCKER to decide (tell main): Exp/MulOverflow library summaries do not preserve `fsBase` (and MulOverflow not `df`)
`Kept s s'` (SumC64) includes `s'.fsBase = s.fsBase ∧ s'.df = s.df` and ScanPost uses it. ExpMain.exp_summary post has df but NOT fsBase; MoLib.mo_summary post (ABIReturn + values) has NEITHER. Janus ABIReturn itself is only sp/fp/g/xmm15. I carried the missing facts as extra conjuncts in `ExpSumm` (fsBase) and `MoSumm` (fsBase, df) in ScanA7, so the final discharge from the real library summaries is NOT possible as is. Options: (a) drop fsBase/df from the Scan (amd64) `Kept` in ScanPost/SciPost (arm64 has neither; spec change -> tell FV-SA3), cheap: remove conjuncts in ExpSumm/MoSumm and the `qfs/hfs/qdf` uses; (b) strengthen the libs (re-run ExpMain 64M-heartbeat proof and MoLib cases A-E) or ask the Janus owners for a generic `Program.Steps` fsBase/df frame lemma (like Steps.regions in RunRegions.lean: needs an exec_regok-style proof; df additionally needs "no CLD/STD/POPF" for the callee code).
## Environment notes
* The shared kept workspace was GC'd. Scratch workspace: /srv/fv-uint256-wsc/work/ws (lake env lean); `.lake/package-overrides.json` points janus to /srv/fv-uint256-wsc/lean/.lake/packages/janus; Extracted olean built from build/ex2-amd64-Scan/Extracted.lean (the artifact used by logs/sc/v3.sh); library oleans copied from lean/.lake/build. Scripts: work/t.sh FILE (copy from lean/ and typecheck), work/cc.sh FILE (compile to olean).
* Heartbeats: one declaration = one budget, so a theorem that runs the stepper and then post-processes must be split (call lemma vs post lemma). `Classical.byContradiction`, not `by_contra`/`swap`/`norm_num` (not available).
* Stepper branch forms seen: `cmp rcx,2`: `(2^64-2 - i + n) % 2^64 = 0`; `cmp dl,0x30`: `setWidth 8 (setWidth 64 (setWidth 32 (ofNat 8 x))) - 48#8 = 0#8`; `ja` after `cmpq $0x4d`: `¬ x < 77 ∧ ¬ x - 77 = 0`; `test bl,bl`: `setWidth 8 (S7.regs 3) = 0#8`; or-chain: `decide ((a ||| b ||| c).toNat = 0)` with `BitVec.ofNat 64 limb`.
## Remaining TODO order
1. Decide the fsBase/df blocker (above).  2. Level-A glue lemma over sci entry (len0 -> sci_len0; else sci_ibs then by idx: sci_none / sci_some; PostK bridging).  3. Level B (Scan wrapper: nil / string / []byte via slicebytetostring live contract / unsupported via newobject).  4. Final theorem: discharge hsfd (SfdLib.hsfd_of_link from FV-I5 -- check /srv/fv-uint256-wi/NOTES-I.md last section), hibs (ibs_lib_A + CodeIn), hexp (ExpMain.exp_summary via CodeIn.lib_summary_link + LinkEq.DataLoaded.of_subset), hmo (MoLib.mo_summary via lib_summary_link).  5. Witnesses (Scan.Witness.nonvacuous per case) and one janus verify; scripts/no-sorry.sh.
