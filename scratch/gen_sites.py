HDR = """import Extracted
import Fv256.FormatFastDefsA64
import Fv256.FormatFastFactsA64
import Fv256.Arm64.FormatFastW
import Fv256.Arm64.FormatFastPF
import Fv256.Arm64.FormatFastB

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64

namespace Fv256.Arm64.FormatFast
"""
BIG=0x204
# n, start, cont, R, fn, na, args, k (reg index of tested result)
sites = [
 ("p",0x60,0x7c,"RP","fP",1,"(BitVec.ofNat 64 fP) (S.regs 2) (S.regs 3)",1),
 ("f1",0x7c,0x9c,"RF","fF",2,"(BitVec.ofNat 64 0x2b) (BitVec.ofNat 64 fF) (S.regs 3)",0),
 ("f2",0x9c,0xbc,"RF","fF",2,"(BitVec.ofNat 64 0x20) (BitVec.ofNat 64 fF) (S.regs 3)",0),
 ("f3",0xbc,0xe0,"RF","fF",2,"(BitVec.ofNat 64 0x2d) (BitVec.ofNat 64 fF) (S.regs 3)",0),
 ("f4",0xe0,0x100,"RF","fF",2,"(BitVec.ofNat 64 0x30) (BitVec.ofNat 64 fF) (S.regs 3)",0),
 ("f5",0x100,0x11c,"RF","fF",2,"(BitVec.ofNat 64 0x23) (BitVec.ofNat 64 fF) (S.regs 3)",0)]
out = HDR
for (n,st,cont,R,fn,na,args,k) in sites:
    jk = f"j{k}"
    out += f"""
theorem {n}_site (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) ({R} : Res)
    (z tab data : BitVec 64) (ch32 : Nat) (H : Prop) (hH : H)
    (hC : ICallContract (Extracted.program.link impl) {fn} {na} stack 120 rt (fun _ => []) {R} (fun _ => True))
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + {hex(st)}))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) :
    RT (Extracted.program.link impl) S
      [(Extracted.entry + {hex(cont)}, fun S' => FInv rt stack z tab data ch32 S0 S' ∧ H ∧
          ∃ j0 j1 j2, {R} data {args} j0 j1 j2 ∧ {jk}.toNat % 2 = 0),
       (Extracted.entry + {hex(BIG)}, fun S' => FInv rt stack z tab data ch32 S0 S' ∧ H ∧
          ∃ j0 j1 j2, {R} data {args} j0 j1 j2 ∧ ¬ {jk}.toNat % 2 = 0)] :=
  site_rt (fun j0 j1 j2 => {R} data {args} j0 j1 j2) (fun j0 j1 => {jk}.toNat % 2 = 0) H hH
    ({n}_call impl rt stack fW fP fF fWr {R} z tab data ch32 hC S0 S hpc hpre hi)
    (fun S' hr hi2 hb => {n}_cont impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hi2 hb)
    (fun S' hr hi2 hb => {n}_big impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hi2 hb)
"""
out += f"""
theorem w_site (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RW : Res)
    (z tab data : BitVec 64)
    (hW : ICallContract (Extracted.program.link impl) fW 1 stack 120 rt (fun _ => []) RW (fun _ => True))
    (S0 : State) (hpc : S0.pc = BitVec.ofNat 64 (Extracted.entry + 0x44))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) :
    RT (Extracted.program.link impl) S0
      [(Extracted.entry + 0x60, fun S' => FInv rt stack z tab data ((S0.regs 3).toNat % 2 ^ 32) S0 S' ∧ True ∧
          ∃ j0 j1 j2, RW data (BitVec.ofNat 64 fW) data (S0.regs 3) j0 j1 j2 ∧ j1.toNat % 2 = 0),
       (Extracted.entry + 0x204, fun S' => FInv rt stack z tab data ((S0.regs 3).toNat % 2 ^ 32) S0 S' ∧ True ∧
          ∃ j0 j1 j2, RW data (BitVec.ofNat 64 fW) data (S0.regs 3) j0 j1 j2 ∧ ¬ j1.toNat % 2 = 0)] :=
  site_rt (fun j0 j1 j2 => RW data (BitVec.ofNat 64 fW) data (S0.regs 3) j0 j1 j2) (fun j0 j1 => j1.toNat % 2 = 0) True trivial
    (w_call impl rt stack fW fP fF fWr RW z tab data hW S0 hpc hpre)
    (fun S' hr hi2 hb => w_cont impl rt stack fW fP fF fWr z tab data _ S0 S' hr hpre hi2 hb)
    (fun S' hr hi2 hb => w_big impl rt stack fW fP fF fWr z tab data _ S0 S' hr hpre hi2 hb)

end Fv256.Arm64.FormatFast
"""
open('/srv/fv-uint256-wf3/lean/Fv256/Arm64/FormatFastSites.lean','w').write(out)
