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
