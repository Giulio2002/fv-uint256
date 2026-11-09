# NOTES-III: amd64 Format path (iii), IntoBig + static math/big.(*Int).Format. HANDOVER (engine agent, 2026-11-07)

Goal: `lean/Fv256/Proofs/Amd64/FormatBig.lean`, a sorry-free Reaches-style lemma from the big-path label (Format entry + 0x1cc) to the function's return, as specified in the last section of NOTES-FORMAT.md ("EXACT interface for (iii)"). Not started: no FormatBig.lean exists. What exists is the IntoBig proof chain retargeted at Format's extraction, compiled and measured.

## 1. The generated IntoBig chain (done)
* Script: `scripts/gen-fm-intobig-amd64.sh LEAN_DIR` (committed on fv/wgiii). It reads the ToBig modules `lean/Fv256/Proofs/Amd64/TB/IntoBig{Defs,FinF,Close,Loop,Tail,Slow3,Mid,T}.lean` (these ARE committed; they are IntoBig's proofs retargeted at ToBig's extraction, where IntoBig is the second segment at ToBig+0x60) and writes `lean/Fv256/Proofs/Amd64/FM/*.lean` (generated, not committed): `(Extracted.entry + 0x60)` becomes `ibE` (`def ibE : Nat := 0x4b1760`, IntoBig's entry in Format's extraction), and `import ...TB.` becomes `import ...FM.`. The module namespace `Fv256.Amd64.IntoBig` is unchanged, so one file imports the TB chain or the FM chain, never both.
* Run: `bash scripts/gen-fm-intobig-amd64.sh lean` from the repo root, then compile in order: Fv256.Spec, SpecC, Util, UtilC, IntoBigCommon, then FM.IntoBigDefs, FinF, Close, Loop, Tail, Slow3, Mid, T. Extraction: the shared one, `/srv/fv-uint256-wf2/build/ex2-amd64-Format/Extracted.lean` (Format entry 0x4b1fc0, IntoBig segment base 0x4b1760).
* IntoBig's offset in Format's extraction is hard-coded in the generator (0x4b1760). If the extraction changes, change it there.
* My scratch build scripts (not in the repo): /srv/janus-ops/s1.a9RI/s16/fm-build2.sh (compiles named modules into a lib dir with `/usr/bin/time -v`, peak RSS in fm/<module>.time), fm1.sh, fm2.sh, fm3.sh. They use `lake env lean -R <lean dir> -o <lib>/<Mod>.olean` with LEAN_PATH = /srv/janus-icall/.lake/build/lib/lean:<lib>, and a lib dir holding Extracted.olean compiled from the extraction. Janus lib used: /srv/janus-icall (agent/icall, same framework as d52a1656 plus later ICall commits).

## 2. The precondition trim (why the chain is cheap)
Format's extraction has TEN read-only data objects (`.rodata+0xbb00 ... +0x363b0`); ToBig's has two. `janus64_data hd [hw]` (used in IntoBigT and IntoBigTail) adds one disjointness fact per object of the data list of the program in `hd : p.DataLoaded mem`; with ten objects `IntoBigTail` grew to 50+ GB (killed at ~1245 s, memcap 58G). ToBig's original: 104 s, 6.9 GB. Entry as a numeral vs a def was NOT the cause (I tested both).
Fix (in the generator, for `FM/IntoBigDefs.lean` only): `Pre` (the statement piece) says `Pib.DataLoaded s.mem` instead of `Extracted.program.DataLoaded s.mem`, with
```
def ibData : List Janus.DataSegment := Extracted.program.data.filter fun d => d.name == ".rodata+0xdc80" || d.name == ".rodata+0x19ba0"
def Pib : Amd64.Program := { Extracted.program with data := ibData }
theorem Pib_dataLoaded {m} (h : Extracted.program.DataLoaded m) : Pib.DataLoaded m := fun d hd => h d (List.mem_filter.1 hd).1
```
(.rodata+0xdc80 holds `arrType`, .rodata+0x19ba0 holds `bigType`; `flagAddr` is runtime.writeBarrier in .noptrbss, a writable region, read through the memory facts, not data.) Result: Tail 114 s / 7.0 GB; Defs 2.0, FinF 2.2, Close 2.3, Loop 2.1, Slow3 2.3, Mid 2.6, T 2.9 GB (peak RSS). All under the default 24 GB per-job cap, no splitting needed.
Consequence for FormatBig: the IntoBig `correctness` theorem (FM.IntoBigT) has the precondition `Pre R b z bp s ∧ PreX z bp s` with `Pib.DataLoaded s.mem`; FormatBig has the full `Extracted.program.DataLoaded` and gets Pib's by `Pib_dataLoaded`. The values `bigType = 5065632 (0x4d4ba0)`, `arrType = 5016704 (0x4c8c80)`, `flagAddr = 6156064 (0x5dcdc0)` are computed by `ripTarget` from IntoBig's code (evaluate with `#eval (bigType, arrType, flagAddr)` after importing FM.IntoBigDefs).

## 3. The big path: code facts (amd64, Format at 0x4b1fc0, harness-amd64 of /srv/fv-uint256-wf2/build)
Frame: entry RSP = sp0 ([sp0] = return address). `push rbp` (sp0-8), `sub rsp,0x40`: at the big label RSP = SP' = sp0 - 0x48. Spills (written by the prologue, 0x50.. are in the CALLER's argument-spill area): 0x50(SP')=z (rax), 0x58=tab (rbx, the fmt.State itab), 0x60=data (rcx), 0x68=ch (edi, 32 bit). The 8-byte slot at 0x28(SP') is the `*big.Int` result.
```
0x4b218c  MOVQ $0x0, 0x28(SP)          ; slot := 0
0x4b2195  MOVQ 0x50(SP), AX            ; z
0x4b219a  LEAQ 0x28(SP), BX            ; &slot
0x4b21a0  CALL IntoBig                 ; (*uint256.Int).IntoBig(b **big.Int)
0x4b21a5  MOVQ 0x28(SP), AX            ; the *big.Int
0x4b21aa  MOVQ 0x58(SP), BX            ; tab
0x4b21af  MOVQ 0x60(SP), CX            ; data
0x4b21b4  MOVL 0x68(SP), DI            ; ch
0x4b21b8  CALL math/big.(*Int).Format  ; static; contractAddr "math/big.(*Int).Format"
0x4b21bd  ADDQ $0x40, SP ; POPQ BP ; RET
```
Reached from +0x2022 (JNE after Width), +0x2040 (JMP after Precision) and +0x1cc generally when width/precision/flag is set or the verb is not d/v/s/x (path (ii) decides that; (iii) starts at the label).
IntoBig call: AX = z, BX = &slot = SP'+0x28; call pushes the return address, so the callee's RSP = SP'-8. ToBig does the same with its own frame (bp = entry RSP - 16 there). In ToBig.lean the callee precondition is `PreC R b z bp sc` at the call-time state `sc`, produced by `janus64_run ... calls [S']` with `S' = Summary.mono S ...`: copy `hx_IB`, `P0`, `PreC`, `pre_mono`, the `hcn`/`hnew'`/`hwb1'`/`hwb2'` setup and `Ensures.toSummaryIn (Fv256.Amd64.IntoBig.correctness impl R b z bp hnew' hwb1' hwb2') (hx_IB impl hI) (by show 2 ≤ 9; decide) (codeIn_restrict_of_apart64 hI [nmIB])` from Fv256/Proofs/Amd64/ToBig.lean (lines ~76-150) and shift the offsets: PreC's `Outside ((s.regs 4).toNat - 4128) 4152 R.rt`, `StackGuardOK s 4128`, etc. are relative to the CALL-TIME RSP (= S.rsp - 8).
Static call: `math/big.(*Int).Format(b *Int, s fmt.State, ch rune)`, Go ABIInternal amd64: RAX = b (the *big.Int), RBX = s.itab, RCX = s.data, RDI = ch (32 bit). `nargs = 4`. Call-time RSP = SP'-8 again. The frame to protect from the callee is [RSP_call, RSP_call + 120): the slot, the spills up to SP'+0x70, and the return address at SP'+0x48 are inside.

## 4. The statement (agreed shape; FV-F3 uses the same on arm64)
```
theorem big_path (impl) (hI : ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (hnew : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb1 hwb2 : WbLiveContract64 ... "runtime.gcWriteBarrier1"/"...2" 4096 R 1/2)
    (stack : Nat) (rt : List (Nat × Nat)) (RBf : Res) (z tab data ch : BitVec 64) (S0 S : State) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret)
    (hBf : ICallContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "math/big.(*Int).Format") 4 stack 120 rt (fun _ => []) RBf
        (fun sc => ∃ P, (sc.regs 0).toNat = P ∧ BigObj sc.mem P (val256 S0.mem z.toNat) ∧ sc.regs 3 = tab ∧ sc.regs 1 = data ∧ (sc.regs 7).toNat % 2^32 = ch.toNat % 2^32))
    ... facts about S (rip = Format entry + 0x1cc, rsp = S0.rsp - 0x48, the spills = z,tab,data,ch, the IntoBig Pre facts, Outside of the frame wrt R.rt AND rt, CodePtrOK nothing needed for the static call):
    Reaches ((Extracted.program.link impl).withExit ret) S (IsReturn fun S' => ABIReturn S0 S' ∧ BigPost ...)
```
`BigPost`: returned, rsp/rbp restored, `*z` unchanged, `MemFrame S.mem S'.mem (R.rt ++ rt ++ stack windows)`, plus `RBf` on the callee's results (existential, forwarded unchanged). P of the call (the ICall call-site obligation) is `BigObj`/`val256` of z: it is proved from IntoBig's `Post` (`BigObj s'.mem P (val256 s.mem z.toNat)`, see ToBig: `hbig hbr`, `BigObj.of_bigOut`) and the facts that the frame writes do not touch z (`val256` reads z's 32 bytes: Disjoint z, as in ToBig's `hv`). P must not mention impl/rt/R (audit); S0, z, tab, data, ch are statement variables, fine. Open point (flagged by FV-G): the audit has not yet been shown to accept RtInv R (allocator) together with IfaceModel R' (typeAssert) in one theorem; use distinct names and `open Janus.Contracts.IfaceAmd64` only, not Iface.
Pitfalls from my ICall work: contracts about `Extracted.program.link impl` need `calls [h]` with the hypothesis whose entry for a static callee is `Extracted.program.contractAddr "..."` (a numeral after evaluation); `Outside a n rt` hypotheses in context are used by `MemFrame` rewriting through `Outside.of_sub` (state them as `Outside` facts, with the exact forms the call produces, e.g. `(sp - 8 - 32 - 8)`-style subtractions; I used `have h' : Outside (...) (...) rt := h.of_sub (by omega) (by omega)` before `janus64_run`); `fn`-like itab links are not needed here (the callee is static); after `janus64_run` the callee-post facts are inaccessible names: use `rename_i` / `janus_assumption` (not `assumption`).

## 5. Plan (cut at callee returns, <= ~200k heartbeats per declaration)
1. Statement pieces file `FormatBigDefs.lean` (BigPre, BigPost, P of the call).
2. Lemma A: label -> IntoBig return: from S, `movq $0,0x28(rsp)`, set AX/BX, call IntoBig through `S'` (copy of ToBig's `S'`), conclude an abstract mid state S1 (after the call, rip = +0x1a5... 0x4b21a5) with: `BigObj` of z at the slot value, `MemFrame` against R.rt ++ the IntoBig window, spills intact (they are above the callee's window; the slot is the callee's output `bp`). Models: ToBig.lean (the whole proof is this plus an epilogue), Fv256/Proofs/Amd64/ErlpP1b.lean.
3. Lemma B: S1 -> return: reload AX/BX/CX/DI from the slot/spills (memory facts from A), call the static Format through `hBf` (`janus64_run ... calls [hBf]`), `ADDQ $0x40,SP; POPQ BP; RET`; prove P at the call from A's BigObj; post from the ICall post (`ICallRet64`: junk registers, `MemFrame ... (rt ++ calleeStack64 ...)`). Model: /srv/fv-uint256-wr/lean/Fv256/Proofs/Amd64/ErlpCall.lean (`erlp_call`: Reaches from a mid state with relations `S2.regs 4 = s.regs 4 - 48#64` etc.).
4. `big_path` = A then B (`Reaches` composition lemma used in ErlpP1b/ErlpS1m). Witness theorems and the arm64 twin (`FormatBigA64.lean`, FV-F3 is on arm64 in /srv/fv-uint256-wf3) are separate.
5. Re-verification of the FM chain is part of every full Format verify (~7 min cold, 7 GB peak).

## 6. Other state to know
* Engine: janus agent/icall (fba902c1) is the Janus to pin: abstract callees (`ICallContract[64]`, `preserves` parameter by the upstream worker), static stub callee allowance, example witnesses. /srv/janus-icall/bin/janus is built at fba902c1 (rebuild if you change Janus).
* Memory rules: memcap every lean command (the FM chain fits in 24 GB; my scratch scripts used 58G only while diagnosing); one heavy job at a time; LEAN_NUM_THREADS <= 4; never kill by pattern.
* My notes on the 50 GB diagnosis: ToBig original TB chain measurements (peak RSS KB: Defs 2.0M, FinF 2.2M, Close 2.3M, Loop 2.1M, Tail 6.9M) in /srv/janus-ops/s1.a9RI/s16/tbm1.log; FM chain after the trim in fm2.log and fm3.log of the same directory.

## DELIVERED (FV-BG, 2026-11-07): lean/Fv256/Proofs/Amd64/FormatBig.lean `Fv256.Amd64.FormatBig.big_path`, sorry-free (propext, Classical.choice, Quot.sound)
Files: FormatBigDefs (BigR2, BigQ, bigObj_writeLE), FormatBigA (IntoBig half: call_pre, mid_of_post, after_setup, big_A), FormatBigB (static big.Format call), FormatBig (composition). Pin n10 51d592da (lakefile/manifest). Build: run scripts/gen-fm-intobig-amd64.sh (now also applies scripts/patch-fm-intobig-amd64.py), compile FM chain (~11 min, 7 GB peak in Tail), then Fv256.Amd64.FormatBigDefs/A/B/FormatBig (seconds).
The generator patch adds a 5th conjunct to IntoBig's `Post` (fresh block + word block lie in R.rt when *bp = 0): amd64 pushes a return address before the second call, so BigObj must be shown to survive a store outside R2.rt.
Differences from hbig in Format.lean: (1) BigQ's frame now also lists the slot (r+0x28,r+0x30) (the old BigQ omitted it: unprovable); BigQ is redefined in FormatBigDefs with that frame. (2) extra hypotheses: DataLoaded at S (not S0), BigR2 (guard margin 4136 below r, g+16/z/bigType/arrType outside R2.rt, flagAddr readable, 4 R2.ok, budget), hret47, hdf0/hx0, hg1 hg2 hgo hgd (g facts as in fast_amd64), stack >= 4568. (3) NotPlain not needed.
