import Extracted
import Fv256.Proofs.Common.FormatFastDefsA64
import Fv256.Proofs.Common.FormatFastFactsA64
import Fv256.Proofs.Arm64.FormatFastHexSum
import Fv256.Proofs.Common.GrabTac

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64

namespace Fv256.Arm64.FormatFast

set_option janus.callRegions true in
set_option maxRecDepth 100000 in
/-- the `x` path: `Hex(z)` from `Format+0x19c`, return at `Format+0x1a4` -/
theorem hex_call (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (stack fW fP fF fWr : Nat)
    (z tab data : BitVec 64) (ch32 : Nat) (hI : ImplApart Extracted.program impl)
    (hc : RtContract (P0H impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x19c))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (h4208 : 4208 ≤ stack) (hdl : Extracted.program.DataLoaded S0.mem)
    (hdrt : ∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length rt) (hreg : S.mem.regions = S0.mem.regions)
    (ht1 : Outside 968614 256 rt)
    (hg : GuardOK S0 0) (hgo : Outside ((S0.regs 28).toNat + 16) 8 rt)
    (hgd : (S0.regs 28).toNat + 24 ≤ S0.sp.toNat - stack ∨ S0.sp.toNat + 0x78 ≤ (S0.regs 28).toNat + 16)
    (hHx : ∀ M, MemFrame S0.mem M (FL rt S0.sp.toNat stack) → ∀ n, Fv256.C.hexDigits (val256 S0.mem z.toNat) n →
      H [0, S0.sp.toNat - 112 + 38 + (64 - n), n + 2] (S0.regs 28).toNat (S0.sp.toNat - 112) (rtView rt M)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1a4)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧
        Fv256.Hex.HexOut (val256 S0.mem z.toNat) S'.mem (S'.regs 0).toNat (S'.regs 1).toNat ∧
        InRanges (S'.regs 0).toNat (S'.regs 1).toNat rt ∧
        S'.mem.regions = S0.mem.regions ∧ Extracted.program.DataLoaded S'.mem) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, ifr, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0', h1', h2', h29', hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  have hdlS : Extracted.program.DataLoaded S.mem := by
    refine dataLoaded_frame (m := S0.mem) hdl hreg ifr (fun d hd => ?_)
    have hdj := dataLoaded_disjoint hdl hd hwa0
    simp only [FL, outside_append, outside_cons, outside_nil]
    refine ⟨hdrt d hd, ?_, ?_, ?_, trivial⟩ <;> omega
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hgS : S.mem.readLE ((S0.regs 28).toNat + 16) 8 = S0.mem.readLE ((S0.regs 28).toNat + 16) 8 :=
    ifr.readLE _ _ (out_fl hgo (by omega) hwb)
  have hgaS : S.mem.accessible ((S0.regs 28).toNat + 16) 8 false = true := by rw [ifr.accessible]; exact hg2
  have hvS : val256 S.mem z.toNat = val256 S0.mem z.toNat := hzr
  have hHS : ∀ n, Fv256.C.hexDigits (val256 S0.mem z.toNat) n →
      H [0, S0.sp.toNat - 112 + 38 + (64 - n), n + 2] (S0.regs 28).toNat (S0.sp.toNat - 112) (rtView rt S.mem) :=
    hHx S.mem ifr
  simp only [Spec.val256_limbs] at hHS
  have hout8 : Outside (S0.sp.toNat - 4208) (4208 + 8) rt := hout.of_sub (by omega) (by omega)
  janus_run [i88, hwa, hdlS, hgaS, hHS, hvS, hgS, i4, i28] until [Extracted.entry + 0x1a4] calls [hex_summary impl rt H z hI hc]
  rename_i hrip h4 h28' h29' h18' hIn hfrD hHO
  rw [← Spec.val256_limbs S0.mem z.toNat] at hHO
  have hfin : FInv rt stack z tab data ch32 S0 s' :=
    finv_call1 hi' hst hout (k := 4208) h4208 hfrD (by simp [h4, i4, setReg_apply]) (by simp [h29', i29, setReg_apply])
      (by simp [h28', i28, setReg_apply]) (by simp [h18', i18, setReg_apply]) rfl
  refine ReachesRet.done ?_ ⟨hfin, hHO, hIn, hrg1.trans hreg, ?_⟩
  · simp [hrip, Extracted.entry, setReg_apply]
  · refine dataLoaded_frame (m := S0.mem) hdl (hrg1.trans hreg) hfin.2.2.2.2.1 (fun d hd => ?_)
    have hdj := dataLoaded_disjoint hdl hd hwa0
    simp only [FL, outside_append, outside_cons, outside_nil]
    refine ⟨hdrt d hd, ?_, ?_, ?_, trivial⟩ <;> omega

end Fv256.Arm64.FormatFast
