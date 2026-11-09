import Extracted
import Fv256.Proofs.Common.FormatFastDefs
import Fv256.Proofs.Common.FormatFastFacts
import Fv256.Proofs.Amd64.FormatFastHexSum
import Fv256.Proofs.Common.GrabTac
import Fv256.Proofs.Common.UtilE

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.IfaceAmd64
open Fv256.FormatFast

namespace Fv256.Amd64.FormatFast

set_option janus.callRegions true in
set_option maxRecDepth 100000 in
/-- the `x` path: `Hex(z)` from `Format+0x176`, return at `Format+0x185` -/
theorem hex_call (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (stack fW fP fF fWr : Nat)
    (z tab data : BitVec 64) (ch32 : Nat) (hI : ImplApart Extracted.program impl)
    (hc : RtContract64 (P0H impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x176))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (h4208 : 4208 ≤ stack) (hdl : Extracted.program.DataLoaded S0.mem)
    (hdrt : ∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length rt) (hreg : S.mem.regions = S0.mem.regions)
    (ht1 : Outside 5142664 256 rt)
    (hg1 : (S0.regs 14).toNat + 24 ≤ 2 ^ 48) (hg2 : S0.mem.accessible ((S0.regs 14).toNat + 16) 8 false = true)
    (hg3 : S0.mem.readLE ((S0.regs 14).toNat + 16) 8 < (S0.regs 4).toNat - 8)
    (hgo : Outside ((S0.regs 14).toNat + 16) 8 rt)
    (hgd : (S0.regs 14).toNat + 24 ≤ (S0.regs 4).toNat - 8 - stack ∨ (S0.regs 4).toNat + 0x78 ≤ (S0.regs 14).toNat + 16)
    (hx0 : S0.xmm 15 = 0) (hdf0 : S0.df = false)
    (hHx : ∀ M, MemFrame S0.mem M (FL rt (S0.regs 4).toNat stack) → ∀ n, Fv256.C.hexDigits (S0.mem.readLE z.toNat 32) n →
      H [0, (S0.regs 4).toNat - 8 - 112 + 38 + (64 - n), n + 2] (S0.regs 14).toNat ((S0.regs 4).toNat - 8 - 112) (rtView rt M)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x185)) S
      (fun S' => FInvD rt stack z tab data ch32 S0 S' ∧
        Fv256.Hex.HexOut (S0.mem.readLE z.toNat 32) S'.mem (S'.regs 0).toNat (S'.regs 3).toNat ∧
        InRanges (S'.regs 0).toNat (S'.regs 3).toNat rt ∧
        S'.mem.regions = S0.mem.regions ∧ Extracted.program.DataLoaded S'.mem) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  have hpre0 := hpre
  obtain ⟨h0', h3', h1', h5, hal, hwb, hwn, hwa0, hout, hs58, hs60, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzb, hza0, hzo, hzd⟩ := hpre0
  have hwb0 := hwb
  have hout0 := hout
  have hdlS : Extracted.program.DataLoaded S.mem := by
    refine dataLoaded_frame (m := S0.mem) hdl hreg ifr (fun d hd => ?_)
    have hdj := Fv256.E.dataLoaded_disjoint hdl hd hwa0
    simp only [FL, outside_append, outside_cons, outside_nil]
    refine ⟨hdrt d hd, ?_, ?_, trivial⟩ <;> omega
  have hgS : S.mem.readLE ((S0.regs 14).toNat + 16) 8 = S0.mem.readLE ((S0.regs 14).toNat + 16) 8 :=
    ifr.readLE _ _ (out_fl hgo (by omega) hwb)
  have hgaS : S.mem.accessible ((S0.regs 14).toNat + 16) 8 false = true := by rw [ifr.accessible]; exact hg2
  have hvS : S.mem.readLE z.toNat 32 = S0.mem.readLE z.toNat 32 := hzr
  have hHS : ∀ n, Fv256.C.hexDigits (S0.mem.readLE z.toNat 32) n →
      H [0, (S0.regs 4).toNat - 8 - 112 + 38 + (64 - n), n + 2] (S0.regs 14).toNat ((S0.regs 4).toNat - 8 - 112) (rtView rt S.mem) :=
    hHx S.mem ifr
  janus64_run [i50, hwa, hdlS, hgaS, hHS, hvS, hgS, valueAt, Janus.Arm64.Memory.readLE_writeLE_of_disjoint] until [Extracted.entry + 0x185] calls [hex_summary impl rt H z hI hc]
  rename_i hrip h4 h5 h14 hx hIn hHO hfrD
  have h8 : 8 ≤ (S0.regs 4).toNat := by omega
  have hfin : FInvD rt stack z tab data ch32 S0 s' :=
    finvD_call1 hi'.toD hwb0 hout0 h4208 hfrD (by simp [setRegF_apply, h4, i4, sub_add8])
      (by simp [setRegF_apply, h5]) (by simp [setRegF_apply, h14]) (by simp [hx]) rfl
  refine ReachesRet.done ?_ ⟨hfin, hHO, hIn, hrg1.trans hreg, ?_⟩
  · rw [hrip]
    simp (disch := omega) only [retAddrOf, setRegF_apply, ite_true, sub8_toNat _ h8, Janus.Arm64.Memory.readLE_writeLE_self]
    simp [Extracted.entry]
  · refine dataLoaded_frame (m := S0.mem) hdl (hrg1.trans hreg) hfin.2.2.2.2.1 (fun d hd => ?_)
    have hdj := Fv256.E.dataLoaded_disjoint hdl hd hwa0
    simp only [FL, outside_append, outside_cons, outside_nil]
    refine ⟨hdrt d hd, ?_, ?_, trivial⟩ <;> omega

end Fv256.Amd64.FormatFast
