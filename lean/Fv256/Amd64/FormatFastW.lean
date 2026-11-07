import Extracted
import Fv256.GrabRet
import Fv256.FormatFastDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.IfaceAmd64
open Fv256.FormatFast Fv256.GrabRet

namespace Fv256.Amd64.FormatFast

/-- site W: spills, `Width()` icall (itab+0x28), return at `Format+0x5c` -/
theorem w_call (impl : List Amd64.Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RW : Res)
    (z tab data : BitVec 64)
    (hW : ICallContract64 (Extracted.program.link impl) fW 1 stack 80 rt (fun _ => []) RW (fun _ => True) (RtPreserves64 R2))
    (S0 : State) (hpc : S0.rip = BitVec.ofNat 64 (Extracted.entry + 0x45))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0)
    (hwR : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) R2.rt) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x5c)) S0
      (fun S => FInv rt stack z tab data ((S0.regs 7).toNat % 2 ^ 32) S0 S ∧ RPres R2 S0 S ∧
        ∃ j0 j3 j1, RW data tab data (S0.regs 7) j0 j3 j1 ∧ S.regs 0 = j0 ∧ S.regs 3 = j3) := by
  obtain ⟨h0, h3, h1, h5, hal, hwb, hwn, hwa, hout, hs58, hs60, hfW, hfP, hfF, hfWr, htb, hta, hF, hP, hW', hWr, hto, htd, hzb, hza, hzo, hzd⟩ := hpre
  simp only [CodePtrOK64] at hfW
  janus64_run [hs58, hs60, hW', hwa, hta] until [Extracted.entry + 0x5c] calls [hW]
  fv_ret_names junk f x yh m zh kr hpr hfr hR
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
      by simp [callRegs64_apply, setRegF_apply], by simp, trivial, trivial, hF1, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hfr.readLE _ _ (out_cs1 hout hwb (by omega) (by omega))]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod8]
    · rw [hfr.readLE _ _ (out_cs1 hout hwb (by omega) (by omega))]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod8]
    · rw [hfr.readLE _ _ (out_cs1 hout hwb (by omega) (by omega))]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod8, hs60]
    · rw [hfr.readLE _ _ (out_cs1 hout hwb (by omega) (by omega))]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod4]
    · refine rpres_call hpr (by simp [setRegF_apply]) (fun L => ?_) (by simp [callRegs64_apply, setRegF_apply]) rfl
      have hO : ∀ a n, (S0.regs 4).toNat - 8 - stack ≤ a → a + n ≤ (S0.regs 4).toNat - 8 - stack + (stack + 128) → Outside a n R2.rt :=
        fun a n h1 h2 => hwR.of_sub h1 h2
      show Janus.Contracts.view R2.rt L ((((S0.mem.writeLE _ 8 _).writeLE _ 4 _).writeLE _ 8 _).writeLE _ 8 _) = _
      rw [Janus.Contracts.view_writeLE_out (hO _ _ (by omega) (by omega)), Janus.Contracts.view_writeLE_out (hO _ _ (by omega) (by omega)),
        Janus.Contracts.view_writeLE_out (hO _ _ (by omega) (by omega)), Janus.Contracts.view_writeLE_out (hO _ _ (by omega) (by omega))]
    · exact ⟨junk 0, junk 3, junk 1, hR, by simp [callRegs64_apply, setRegF_apply], by simp [callRegs64_apply, setRegF_apply]⟩

set_option hygiene false in
macro "fin_bigW" : tactic => `(tactic| exact ReachesRet.done (by simp [Extracted.entry]) ⟨finv_of hi rfl rfl rfl rfl rfl rfl rfl, rfl⟩)

/-- after `Width()`: `hasWidth == false` continues with the `Precision` setup (`Format+0x68`) -/
theorem w_cont (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x5c))
    (hi : FInv rt stack z tab data ch32 S0 S) (hb : (S.regs 3).toNat % 256 = 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x68)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ S'.regs 3 = S.regs 3 ∧ S'.regs 7 = S.regs 7 ∧ S'.mem = S.mem) := by
  have hb' : BitVec.setWidth 8 (S.regs 3) = 0#8 := (setWidth8_eq_zero _).2 hb
  janus64_run [hb'] until [Extracted.entry + 0x68]
  exact ReachesRet.done (by simp [Extracted.entry]) ⟨finv_of hi rfl rfl rfl rfl rfl rfl rfl, rfl, rfl, rfl⟩

/-- after `Width()`: `hasWidth != false` goes to the big path (`Format+0x1cc`) -/
theorem w_big (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x5c))
    (hi : FInv rt stack z tab data ch32 S0 S) (hb : (S.regs 3).toNat % 256 ≠ 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1cc)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ S'.mem = S.mem) := by
  have hb' : ¬ BitVec.setWidth 8 (S.regs 3) = 0#8 := fun h => hb ((setWidth8_eq_zero _).1 h)
  janus64_run [hb'] until [Extracted.entry + 0x1cc]
  exact ReachesRet.done (by simp [Extracted.entry]) ⟨finv_of hi rfl rfl rfl rfl rfl rfl rfl, rfl⟩

theorem w_site (impl : List Amd64.Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RW : Res)
    (z tab data : BitVec 64)
    (hW : ICallContract64 (Extracted.program.link impl) fW 1 stack 80 rt (fun _ => []) RW (fun _ => True) (RtPreserves64 R2))
    (S0 : State) (hpc : S0.rip = BitVec.ofNat 64 (Extracted.entry + 0x45))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0)
    (hwR : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) R2.rt) :
    RT (Extracted.program.link impl) S0
      [(Extracted.entry + 0x68, fun S => FInv rt stack z tab data ((S0.regs 7).toNat % 2 ^ 32) S0 S ∧ RPres R2 S0 S ∧
          ∃ j0 j3 j1, RW data tab data (S0.regs 7) j0 j3 j1 ∧ S.regs 3 = j3 ∧ j3.toNat % 256 = 0),
       (Extracted.entry + 0x1cc, fun S => FInv rt stack z tab data ((S0.regs 7).toNat % 2 ^ 32) S0 S ∧ RPres R2 S0 S ∧
          ∃ j0 j3 j1, RW data tab data (S0.regs 7) j0 j3 j1 ∧ j3.toNat % 256 ≠ 0)] := by
  refine RT.trans (RT.of_reachesRet (w_call impl R2 rt stack fW fP fF fWr RW z tab data hW S0 hpc hpre hwR)) ?_
  intro t ht S' hr hq
  simp only [List.mem_singleton] at ht
  subst ht
  obtain ⟨hi, hq2, j0, j3, j1, hR, h0, h3⟩ := hq
  by_cases hb : j3.toNat % 256 = 0
  · have k1 : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x68)) S'
        (fun S => FInv rt stack z tab data ((S0.regs 7).toNat % 2 ^ 32) S0 S ∧ RPres R2 S0 S ∧
          ∃ j0 j3 j1, RW data tab data (S0.regs 7) j0 j3 j1 ∧ S.regs 3 = j3 ∧ j3.toNat % 256 = 0) :=
      ReachesRet.mono (w_cont impl rt stack z tab data _ S0 S' hr hi (by rw [h3]; exact hb))
        (fun S'' h => ⟨h.1, (hq2.trans (RPres.of_mem h.2.2.2) hi.2.2.1), j0, j3, j1, hR, h.2.1.trans h3, hb⟩)
    refine RT.widen (RT.of_reachesRet k1) ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨_, List.mem_cons_self .., rfl, fun _ h => h⟩
  · have k1 : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1cc)) S'
        (fun S => FInv rt stack z tab data ((S0.regs 7).toNat % 2 ^ 32) S0 S ∧ RPres R2 S0 S ∧
          ∃ j0 j3 j1, RW data tab data (S0.regs 7) j0 j3 j1 ∧ j3.toNat % 256 ≠ 0) :=
      ReachesRet.mono (w_big impl rt stack z tab data _ S0 S' hr hi (by rw [h3]; exact hb))
        (fun S'' h => ⟨h.1, (hq2.trans (RPres.of_mem h.2) hi.2.2.1), j0, j3, j1, hR, hb⟩)
    refine RT.widen (RT.of_reachesRet k1) ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, fun _ h => h⟩

end Fv256.Amd64.FormatFast
