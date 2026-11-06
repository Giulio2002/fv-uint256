# NOTES-H (FV-H handoff, 2026-11-06)

## Done and verified (fv/wh, f3d166a and earlier; each correctness + Witness.nonvacuous in one janus verify run)
arm64: DivMod, SDiv, SMod, Exp, IExp, Sqrt (50m49 busy host), ISqrt (33m45). amd64: IExp.
Sqrt files: lean/Fv256/Arm64/{SqrtProg,SqrtSum,SqrtSmall,SqrtLimbA,SqrtBig,SqrtEntry,Sqrt,ISqrt}.lean;
tools/gen_sqrt_big_entry.py generates the 3 big-entry cases. Scripts: build/{vsq,visq}.sh (verify), build/li.sh/lp.sh/lisq.sh/lscr.sh (workspace checks).

## Speed debt (parked by main)
SqrtBig.big_loop compiles in 5m14. One `simp (config := {decide := true}) only [setReg_apply, ↓reduceIte, e72, e104] at hf lwv`
(continue branch, ~line 127) costs ~200 s. `simp only [e72,e104]` and `rw [e72,e104]` there do NOT work (later tactics grind >60 min / cap).
Untried idea: do not rewrite hf/lwv at all; use hf.readLE with `by simp [Outside, e72, e104]; omega` and let omega see e72/e104.
Do experiments only on scratch copies (build/lscr.sh, 300 s cap); never edit the main file.

## EncodeRLP: blocked on U-ICALL (UINT256-UPSTREAM.md). Not started.

## Hex amd64 (IN PROGRESS, not proved)
- lean/Fv256/HexSpec.lean (ISA-independent: dig, HexOut, HexQ(arm64), fin_strout, hex_strbytes) compiled and committed. FV-D2 will import it for arm64 Hex.
- lean/Fv256/Amd64/Hex.lean: statement + prefix `janus64_run until [Extracted.entry + 0xec]` + `all_goals sorry`. Check with build/lih.sh (~10 s; workspace fec18988...), real verify build/vhexa.sh (ENDMARK).
- Extraction build/ex-amd64-Hex (--contract runtime.slicebytetostring, hextable at 0x4e7888 (5142664), staticuint64s 0x4f6de0). Code 1199 bytes at 0x4b3600.
- Layout: 66-byte buffer at rsp+0x1e (= sp-74 in arm64 terms), call-site rsp = entry rsp-112; loop head 0x4b36ec; loop body 16 stores per limb with bounds checks `cmp r8,0x42; jae panic`; exit to 0x4b3962 (writes '0','x', computes ptr/len, calls slicebytetostring at 0x4b39a3 with RAX=0,RBX=ptr,RCX=len).
- The prefix has 8 paths (BitLen-style BSR chain on 4 limbs, each guarded by `test rdx,rdx`). Branch conditions have the form `(sshiftRight (if z=0 then -1 else ... BitVec.ofNat 64 (63 - clzNat 64 z)) +1 + ...) .toNat = 0`; infeasible ones need `Fv256.SqrtHead`/`Util.clz_bl`-style facts (see amd64 BitLen.lean and SqrtHead.cl_ne_zero for the pattern).
- Port plan: FV-C's wip/ArmHex.lean.wip has hexbase/hexstep/hexloop (arm64); HexLemmas.lean has st16*, iter_vals, dig_limb. Statement shape: amd64 String.lean (fv/we) is the template (RtContract64 + slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s», rt, H on string ptr sp-112+38+(64-n), len n+2; witness with toy slicebytetostring `constCode64 0 0 0`).
- Then: Witness.nonvacuous, ONE verify of both theorems, COVERAGE row, report.
