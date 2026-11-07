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
