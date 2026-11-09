import Extracted
import Fv256.Proofs.Common.FormatFastDefsA64
import Fv256.Proofs.Common.FormatFastFactsA64
import Fv256.Proofs.Common.GrabRetA64

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64 Fv256.GrabRetA64

namespace Fv256.Arm64.FormatFast

/-- site W: spills, `Width()` icall (itab+0x28), return at `Format+0x5c` -/
theorem w_call (impl : List Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RW : Res)
    (z tab data : BitVec 64)
    (hW : ICallContract (Extracted.program.link impl) fW 1 stack 120 rt (fun _ => []) RW (fun _ => True) (RtPreserves R2))
    (S0 : State) (hpc : S0.pc = BitVec.ofNat 64 (Extracted.entry + 0x44))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0)
    (hwR : Outside (S0.sp.toNat - stack) (stack + 0x78) R2.rt) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x5c)) S0
      (fun S => FInv rt stack z tab data ((S0.regs 3).toNat % 2 ^ 32) S0 S ∧ RPres R2 S0 S ∧
        ∃ j0 j1 j2, RW data (BitVec.ofNat 64 fW) data (S0.regs 3) j0 j1 j2 ∧ S.regs 0 = j0 ∧ S.regs 1 = j1) := by
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta, hF, hP, hW', hWr, hto, htd, hzp, hzo, hzd⟩ := hpre
  simp only [CodePtrOK] at hfW
  have hout8 : Outside (S0.sp.toNat - 8) 128 rt := hout.of_sub (by omega) (by omega)
  janus_run [hs96, hs104, hW', hta, hwa] until [Extracted.entry + 0x5c] calls [hW]
  fv_ret_names_a64 junk f v m ex ep hkeep hpr hfr hR
  have h8 : 8 ≤ stack := hst
  have hs112 : m.readLE (S0.sp.toNat + 112) 4 = (S0.regs 3).toNat % 2 ^ 32 := by
    rw [hfr.readLE _ _ (out_cs hout hst (by omega) (by omega) (by omega))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  have hs88 : m.readLE (S0.sp.toNat + 88) 8 = z.toNat := by
    rw [hfr.readLE _ _ (out_cs hout hst (by omega) (by omega) (by omega))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simpa using Nat.mod_eq_of_lt (show z.toNat < 256 ^ 8 by have := z.isLt; simpa using this)
  have hs96' : m.readLE (S0.sp.toNat + 96) 8 = tab.toNat := by
    rw [hfr.readLE _ _ (out_cs hout hst (by omega) (by omega) (by omega))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simpa using Nat.mod_eq_of_lt (show tab.toNat < 256 ^ 8 by have := tab.isLt; simpa using this)
  have hs104' : m.readLE (S0.sp.toNat + 104) 8 = data.toNat := by
    rw [hfr.readLE _ _ (out_cs hout hst (by omega) (by omega) (by omega))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, hs104]
  refine ReachesRet.done ?_ ⟨?_, ?_, junk 0, junk 1, junk 2, hR, ?_, ?_⟩
  · simp [retStateX, Extracted.entry, setReg_apply]
  · have hF1 : MemFrame S0.mem m (FL rt S0.sp.toNat stack) := by
      unfold FL
      janus_frame
    refine ⟨by simp [retStateX], by simp [retStateX, callRegs_apply, setReg_apply],
      by simp [retStateX, callRegs_apply, setReg_apply], by simp [retStateX, callRegs_apply, setReg_apply], hF1, ?_, ?_, ?_, ?_⟩
    · exact hs88
    · exact hs96'
    · exact hs104'
    · exact hs112
  · refine rpres_call hpr (by simp [setReg_apply]) (fun L => ?_) rfl
    have hO : ∀ a n, S0.sp.toNat - stack ≤ a → a + n ≤ S0.sp.toNat - stack + (stack + 0x78) → Outside a n R2.rt :=
      fun a n h1 h2 => hwR.of_sub h1 h2
    dsimp only
    rw [Janus.Contracts.view_writeLE_out (hO _ _ (by omega) (by omega)), Janus.Contracts.view_writeLE_out (hO _ _ (by omega) (by omega)),
      Janus.Contracts.view_writeLE_out (hO _ _ (by omega) (by omega))]
  · simp [retStateX, callRegs_apply, setReg_apply]
  · simp [retStateX, callRegs_apply, setReg_apply]

end Fv256.Arm64.FormatFast
