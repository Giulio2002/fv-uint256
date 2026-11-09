# NOTES-H (FV-H handoff, 2026-11-06)

## Done and verified (fv/wh, f3d166a and earlier; each correctness + Witness.nonvacuous in one janus verify run)
arm64: DivMod, SDiv, SMod, Exp, IExp, Sqrt (50m49 busy host), ISqrt (33m45). amd64: IExp.
Sqrt files: lean/Fv256/Proofs/Arm64/{SqrtProg,SqrtSum,SqrtSmall,SqrtLimbA,SqrtBig,SqrtEntry,Sqrt,ISqrt}.lean;
tools/gen_sqrt_big_entry.py generates the 3 big-entry cases. Scripts: build/{vsq,visq}.sh (verify), build/li.sh/lp.sh/lisq.sh/lscr.sh (workspace checks).

## Speed debt (parked by main)
SqrtBig.big_loop compiles in 5m14. One `simp (config := {decide := true}) only [setReg_apply, ↓reduceIte, e72, e104] at hf lwv`
(continue branch, ~line 127) costs ~200 s. `simp only [e72,e104]` and `rw [e72,e104]` there do NOT work (later tactics grind >60 min / cap).
Untried idea: do not rewrite hf/lwv at all; use hf.readLE with `by simp [Outside, e72, e104]; omega` and let omega see e72/e104.
Do experiments only on scratch copies (build/lscr.sh, 300 s cap); never edit the main file.

## EncodeRLP: blocked on U-ICALL (UINT256-UPSTREAM.md). Not started.

## Hex amd64 (IN PROGRESS, not proved)
- lean/Fv256/HexSpec.lean (ISA-independent: dig, HexOut, HexQ(arm64), fin_strout, hex_strbytes) compiled and committed. FV-D2 will import it for arm64 Hex.
- lean/Fv256/Proofs/Amd64/Hex.lean: statement + prefix `janus64_run until [Extracted.entry + 0xec]` + `all_goals sorry`. Check with build/lih.sh (~10 s; workspace fec18988...), real verify build/vhexa.sh (ENDMARK).
- Extraction build/ex-amd64-Hex (--contract runtime.slicebytetostring, hextable at 0x4e7888 (5142664), staticuint64s 0x4f6de0). Code 1199 bytes at 0x4b3600.
- Layout: 66-byte buffer at rsp+0x1e (= sp-74 in arm64 terms), call-site rsp = entry rsp-112; loop head 0x4b36ec; loop body 16 stores per limb with bounds checks `cmp r8,0x42; jae panic`; exit to 0x4b3962 (writes '0','x', computes ptr/len, calls slicebytetostring at 0x4b39a3 with RAX=0,RBX=ptr,RCX=len).
- The prefix has 8 paths (BitLen-style BSR chain on 4 limbs, each guarded by `test rdx,rdx`). Branch conditions have the form `(sshiftRight (if z=0 then -1 else ... BitVec.ofNat 64 (63 - clzNat 64 z)) +1 + ...) .toNat = 0`; infeasible ones need `Fv256.SqrtHead`/`Util.clz_bl`-style facts (see amd64 BitLen.lean and SqrtHead.cl_ne_zero for the pattern).
- Port plan: FV-C's wip/ArmHex.lean.wip has hexbase/hexstep/hexloop (arm64); HexLemmas.lean has st16*, iter_vals, dig_limb. Statement shape: amd64 String.lean (fv/we) is the template (RtContract64 + slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s», rt, H on string ptr sp-112+38+(64-n), len n+2; witness with toy slicebytetostring `constCode64 0 0 0`).
- Then: Witness.nonvacuous, ONE verify of both theorems, COVERAGE row, report.

## Hex amd64: VERIFIED 2026-11-06 18:01 (correctness + Witness.nonvacuous in one run, 5m01, pin 655a23fa)
Hex.lean complete (hexstep/hexbase/hexloop, nibble BitVec lemmas, witness with 3-byte-copy toy slicebytetostring). hH is conditional on the actual digit count. build/lihm.sh = fast main iteration (hexstep/hexbase stubbed).

## Hex arm64: VERIFIED 2026-11-06 (correctness + Witness.nonvacuous, one run, 6m47, pin 655a23fa). Extraction build/ex-arm64-Hex from build/harness-arm64 (v1.3.3 master). Scripts build/vhexr.sh, lihr.sh, lihrm.sh. Nibble ASR forms: N{0..3}Eq/H{0..3}Eq/SIEq decide-lemmas.

## PrettyDec (taken over 2026-11-06; FV-D2 has no files). STATE: scoping only, no proof started.
- Re-extracted on the current pin/harness: build/ex-amd64-PrettyDec (8 fns: PrettyDec 871 B @0x4b41a0, udivrem, udivremKnuth, udivremBy1, AppendUint, formatBase10, formatBits, memmove; 5 data objects 1317 B; stubs panicBounds/morestack/panicoverflow)
  and build/ex-arm64-PrettyDec (9 fns, adds math/bits.Div64). Contracts passed: slicebytetostring, growslice, gopanic (check which are actually called).
- Same library functions as Dec => reuse DecProg/ChainProg/LinkEq (fb10_summary, append_summary, udivrem_rem_L_final) but data addresses differ: need gen_libprog with its own --fn/--data (see FV-E handover in NOTES-D.md, fv/wd 28efdca).
- Spec pieces exist: PrettyMath.lean (prettyBytes sep n, plen, pcell, prettyBytes_length/_getD), SpecTxt.prettyBytes_zero.
- Work items: (1) library program + LibIn per ISA; (2) loop invariant for the outer udivrem/AppendUint/copy-with-separator loop (comma counter persists across 19-digit chunks, zero padding of inner chunks); (3) final slicebytetostring call + StrAt; (4) statement + toy-runtime witness (needs a copying toy sbts, as in Hex witness: H restricted to the one call shape).
- Estimate: multi-hour per ISA (Dec took ~16-17 min per verify and many files); not started.
