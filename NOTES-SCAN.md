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
