import Extracted
import Fv256.Proofs.Common.FormatFastDefs
import Fv256.Proofs.Common.FormatFastFacts
import Fv256.Proofs.Common.IntoBigCommon
import Fv256.Proofs.Common.GrabRet
import Fv256.Proofs.Amd64.FormatBigDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFast Fv256.IntoBig

namespace Fv256.Amd64.FormatBig

abbrev fmtAddr : Nat := Extracted.program.contractAddr "math/big.(*Int).Format"

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- the big path, part B: reload `b`, `tab`, `data`, `ch`, the static call `math/big.(*Int).Format(b, s, ch)` from `Format+0x1e5`, epilogue, return -/
theorem big_B (impl : List Amd64.Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack : Nat) (RBf : Res)
    (tab data : BitVec 64) (ch32 P v : Nat) (S0 S1 : State)
    (hBf : ICallContract64 (Extracted.program.link impl) fmtAddr 4 stack 80 rt (fun _ => []) RBf
      (fun sc => ∃ P : BitVec 64, sc.regs 0 = P ∧ BigObj sc.mem P.toNat v ∧ sc.regs 3 = tab ∧ sc.regs 1 = data ∧
        (sc.regs 7).toNat % 2 ^ 32 = ch32))
    (hlt : ch32 < 2 ^ 32) (hBO : BigObj S1.mem P v) (hPin : InRanges P 32 R2.rt) (hAin : InRanges (S1.mem.readLE (P + 8) 8) 32 R2.rt)
    (hpc : S1.rip = BitVec.ofNat 64 (Extracted.entry + 0x1e5))
    (hsp : S1.regs 4 = S0.regs 4) (hal : (S0.regs 4).toNat % 8 = 0) (hwb : 8 + stack ≤ (S0.regs 4).toNat)
    (hwn : (S0.regs 4).toNat + 0x78 ≤ 2 ^ 48)
    (hwa : S1.mem.accessible ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) true = true)
    (hwR : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) R2.rt)
    (hout : Outside ((S0.regs 4).toNat - 8) 128 rt)
    (hs28 : S1.mem.readLE ((S0.regs 4).toNat + 0x28) 8 = P) (hP : P < 2 ^ 64)
    (hs58 : S1.mem.readLE ((S0.regs 4).toNat + 0x58) 8 = tab.toNat) (hs60 : S1.mem.readLE ((S0.regs 4).toNat + 0x60) 8 = data.toNat)
    (hs68 : S1.mem.readLE ((S0.regs 4).toNat + 0x68) 4 = ch32)
    (hr72 : S1.mem.readLE ((S0.regs 4).toNat + 72) 8 = S0.mem.readLE ((S0.regs 4).toNat + 72) 8)
    (hr64 : S1.mem.readLE ((S0.regs 4).toNat + 64) 8 = S0.mem.readLE ((S0.regs 4).toNat + 64) 8)
    (hret : S0.mem.readLE ((S0.regs 4).toNat + 72) 8 < 2 ^ 47) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 72) 8)) S1
      (fun S' => S'.regs 4 = S0.regs 4 + 80#64 ∧ S'.regs 5 = BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 64) 8) ∧
        S'.regs 14 = S1.regs 14 ∧ S'.xmm 15 = S1.xmm 15 ∧
        MemFrame S1.mem S'.mem (rt ++ [((S0.regs 4).toNat - 8 - stack, (S0.regs 4).toNat + 32)]) ∧
        (∃ j0 j3 j1, RBf (BitVec.ofNat 64 P) tab data (BitVec.ofNat 64 ch32) j0 j3 j1)) := by
  have hwa' : S1.mem.accessible ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) true = true := hwa
  have hmodP : P % 2 ^ 64 = P := Nat.mod_eq_of_lt hP
  have hmodC : ch32 % 4294967296 = ch32 := Nat.mod_eq_of_lt hlt
  have hBO' : BigObj (S1.mem.writeLE ((S0.regs 4).toNat - 8) 8 (Extracted.entry + 0x1fd)) P v :=
    bigObj_writeLE hBO hPin hAin (hwR.of_sub (by omega) (by omega))
  have hEx : ∃ P_1 : BitVec 64, BitVec.ofNat 64 P = P_1 ∧ BigObj (S1.mem.writeLE ((S0.regs 4).toNat - 8) 8 (Extracted.entry + 0x1fd)) P_1.toNat v :=
    ⟨BitVec.ofNat 64 P, rfl, by rw [BitVec.toNat_ofNat, hmodP]; exact hBO'⟩
  janus64_run [hEx, hmodP, hmodC, hBO', hs28, hs58, hs60, hs68, hwa', hr72, hr64] calls [hBf]
  fv_ret_names junk f x yh m zh kr hpr hfr hR
  have hc : BitVec.setWidth 64 (BitVec.ofNat 32 ch32) = BitVec.ofNat 64 ch32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have h32 : ch32 % 2 ^ 32 = ch32 := Nat.mod_eq_of_lt hlt
    rw [h32, Nat.mod_eq_of_lt (by omega : ch32 < 2 ^ 64)]
  refine ⟨?_, junk 0, junk 3, junk 1, by rw [← hc]; exact hR⟩
  have h1 : MemFrame S1.mem (S1.mem.writeLE ((S0.regs 4).toNat - 8) 8 (Extracted.entry + 0x1fd))
      (rt ++ [((S0.regs 4).toNat - 8 - stack, (S0.regs 4).toNat + 32)]) :=
    MemFrame.of_writeLE S1.mem _ (r := ((S0.regs 4).toNat - 8 - stack, (S0.regs 4).toNat + 32)) (by simp) (by simp) (by simp; omega)
  refine h1.trans hfr (fun a n h => ?_)
  simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
  obtain ⟨h1, h2⟩ := h
  exact ⟨⟨h1, h2⟩, h1, by omega, by omega⟩

end Fv256.Amd64.FormatBig
