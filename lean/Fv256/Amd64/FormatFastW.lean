import Extracted
import Fv256.FormatFastDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.IfaceAmd64
open Fv256.FormatFast

namespace Fv256.Amd64.FormatFast

/-- site W: spills, `Width()` icall (itab+0x28), return at `Format+0x5c` -/
theorem w_call (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RW : Res)
    (z tab data : BitVec 64)
    (hW : ICallContract64 (Extracted.program.link impl) fW 1 stack 80 rt (fun _ => []) RW (fun _ => True))
    (S0 : State) (hpc : S0.rip = BitVec.ofNat 64 (Extracted.entry + 0x45))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x5c)) S0
      (fun S => FInv rt stack z tab data ((S0.regs 7).toNat % 2 ^ 32) S0 S ∧
        ∃ j0 j3 j1, RW data tab data (S0.regs 7) j0 j3 j1 ∧ S.regs 0 = j0 ∧ S.regs 3 = j3) := by
  obtain ⟨h0, h3, h1, h5, hal, hwb, hwn, hwa, hout, hs58, hs60, hfW, hfP, hfF, hfWr, htb, hta, hF, hP, hW', hWr, hto, htd, hzb, hza, hzo, hzd⟩ := hpre
  simp only [CodePtrOK64] at hfW
  janus64_run [hs58, hs60, hW', hwa, hta] until [Extracted.entry + 0x5c] calls [hW]
  rename_i junk f x yh m zh kr hkeep hfr hR
  have h8 : 8 ≤ (S0.regs 4).toNat := by omega
  refine ReachesRet.done ?_ ?_
  · simp (disch := omega) only [retState64, retAddrOf, setRegF_apply, ite_true, sub8_toNat _ h8,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simp [Extracted.entry]
  · have hF1 : MemFrame S0.mem m (FL rt (S0.regs 4).toNat stack) := by
      unfold FL
      janus_frame
    have rd : ∀ a n, Outside a n (rt ++ [((S0.regs 4).toNat - 8 - stack, (S0.regs 4).toNat - 8),
        ((S0.regs 4).toNat - 8 + 8, (S0.regs 4).toNat - 8 + 8 + 8)]) → m.readLE a n = _ := fun a n h => hfr.readLE a n h
    simp only [retState64, FInv]
    refine ⟨⟨by simp [callRegs64_apply, setRegF_apply, sub_add8], by simp [callRegs64_apply, setRegF_apply],
      by simp [callRegs64_apply, setRegF_apply], by simp, trivial, trivial, hF1, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hfr.readLE _ _ (out_cs1 hout hwb (by omega) (by omega))]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod8]
    · rw [hfr.readLE _ _ (out_cs1 hout hwb (by omega) (by omega))]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod8]
    · rw [hfr.readLE _ _ (out_cs1 hout hwb (by omega) (by omega))]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod8, hs60]
    · rw [hfr.readLE _ _ (out_cs1 hout hwb (by omega) (by omega))]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod4]
    · exact ⟨junk 0, junk 3, junk 1, hR, by simp [callRegs64_apply, setRegF_apply], by simp [callRegs64_apply, setRegF_apply]⟩
