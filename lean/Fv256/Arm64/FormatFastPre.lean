import Extracted
import Fv256.FormatFastDefsA64
import Fv256.FormatFastFactsA64
import Fv256.Arm64.FormatFastSites
import Fv256.Arm64.FormatFastSw

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64

namespace Fv256.Arm64.FormatFast

theorem pre_fast (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RW RP RF : Res)
    (z tab data : BitVec 64)
    (hW : ICallContract (Extracted.program.link impl) fW 1 stack 120 rt (fun _ => []) RW (fun _ => True))
    (hP : ICallContract (Extracted.program.link impl) fP 1 stack 120 rt (fun _ => []) RP (fun _ => True))
    (hF : ICallContract (Extracted.program.link impl) fF 2 stack 120 rt (fun _ => []) RF (fun _ => True))
    (S0 : State) (hpc : S0.pc = BitVec.ofNat 64 (Extracted.entry + 0x44))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) :
    RT (Extracted.program.link impl) S0
      [(Extracted.entry + 0x144, fun S => FInv rt stack z tab data ((S0.regs 3).toNat % 2 ^ 32) S0 S ∧
          (∃ r3 j1, PlainHist RW RP RF data fW fP fF r3 j1) ∧
          (((S0.regs 3).toNat % 2 ^ 32) = 100 ∨ ((S0.regs 3).toNat % 2 ^ 32) = 115 ∨ ((S0.regs 3).toNat % 2 ^ 32) = 118)),
       (Extracted.entry + 0x19c, fun S => FInv rt stack z tab data ((S0.regs 3).toNat % 2 ^ 32) S0 S ∧
          (∃ r3 j1, PlainHist RW RP RF data fW fP fF r3 j1) ∧ ((S0.regs 3).toNat % 2 ^ 32) = 120),
       (Extracted.entry + 0x204, fun S => FInv rt stack z tab data ((S0.regs 3).toNat % 2 ^ 32) S0 S ∧
          NotPlain RW RP RF data fW fP fF (S0.regs 3) ((S0.regs 3).toNat % 2 ^ 32))] := by
  have hlt : ((S0.regs 3).toNat % 2 ^ 32) < 2 ^ 32 := Nat.mod_lt _ (by decide)
  refine RT.trans (w_site impl rt stack fW fP fF fWr RW z tab data hW S0 hpc hpre) ?_
  intro t ht S1 hr1 hq1
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · obtain ⟨hi1, -, j0, j1w, j2, hR1, hb1⟩ := hq1
    have hH1 : WRes RW data fW (S0.regs 3) j1w ∧ j1w.toNat % 2 = 0 := ⟨⟨j0, j2, hR1⟩, hb1⟩
    refine RT.trans (p_site impl rt stack fW fP fF fWr RP z tab data ((S0.regs 3).toNat % 2 ^ 32) _ hH1 hP S0 S1 hr1 hpre hi1) ?_
    intro t ht S2 hr2 hq2
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · obtain ⟨hi2, hHa, j0, j1, j2, hR, hb⟩ := hq2
      have hH2 : ((WRes RW data fW (S0.regs 3) j1w ∧ j1w.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 = 0)) := ⟨hHa, ⟨_, _, j0, j1, j2, hR, hb⟩⟩
      refine RT.trans (f1_site impl rt stack fW fP fF fWr RF z tab data ((S0.regs 3).toNat % 2 ^ 32) _ hH2 hF S0 S2 hr2 hpre hi2) ?_
      intro t ht S3 hr3 hq3
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · obtain ⟨hi3, hHa, j0, j1, j2, hR, hb⟩ := hq3
        have hH3 : (((WRes RW data fW (S0.regs 3) j1w ∧ j1w.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x2b (fun j => j.toNat % 2 = 0)) := ⟨hHa, ⟨_, j0, j1, j2, hR, hb⟩⟩
        refine RT.trans (f2_site impl rt stack fW fP fF fWr RF z tab data ((S0.regs 3).toNat % 2 ^ 32) _ hH3 hF S0 S3 hr3 hpre hi3) ?_
        intro t ht S4 hr4 hq4
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · obtain ⟨hi4, hHa, j0, j1, j2, hR, hb⟩ := hq4
          have hH4 : ((((WRes RW data fW (S0.regs 3) j1w ∧ j1w.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x2b (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x20 (fun j => j.toNat % 2 = 0)) := ⟨hHa, ⟨_, j0, j1, j2, hR, hb⟩⟩
          refine RT.trans (f3_site impl rt stack fW fP fF fWr RF z tab data ((S0.regs 3).toNat % 2 ^ 32) _ hH4 hF S0 S4 hr4 hpre hi4) ?_
          intro t ht S5 hr5 hq5
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · obtain ⟨hi5, hHa, j0, j1, j2, hR, hb⟩ := hq5
            have hH5 : (((((WRes RW data fW (S0.regs 3) j1w ∧ j1w.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x2b (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x20 (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x2d (fun j => j.toNat % 2 = 0)) := ⟨hHa, ⟨_, j0, j1, j2, hR, hb⟩⟩
            refine RT.trans (f4_site impl rt stack fW fP fF fWr RF z tab data ((S0.regs 3).toNat % 2 ^ 32) _ hH5 hF S0 S5 hr5 hpre hi5) ?_
            intro t ht S6 hr6 hq6
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
            rcases ht with rfl | rfl
            · obtain ⟨hi6, hHa, j0, j1, j2, hR, hb⟩ := hq6
              have hH6 : ((((((WRes RW data fW (S0.regs 3) j1w ∧ j1w.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x2b (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x20 (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x2d (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x30 (fun j => j.toNat % 2 = 0)) := ⟨hHa, ⟨_, j0, j1, j2, hR, hb⟩⟩
              refine RT.trans (f5_site impl rt stack fW fP fF fWr RF z tab data ((S0.regs 3).toNat % 2 ^ 32) _ hH6 hF S0 S6 hr6 hpre hi6) ?_
              intro t ht S7 hr7 hq7
              simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
              rcases ht with rfl | rfl
              · obtain ⟨hi7, hHa, j0, j1, j2, hR, hb⟩ := hq7
                have hH7 : (((((((WRes RW data fW (S0.regs 3) j1w ∧ j1w.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x2b (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x20 (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x2d (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x30 (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x23 (fun j => j.toNat % 2 = 0)) := ⟨hHa, ⟨_, j0, j1, j2, hR, hb⟩⟩
                have hpl : ∃ r3 j1, PlainHist RW RP RF data fW fP fF r3 j1 := ⟨_, j1w, hH7⟩
                by_cases hdec : ((S0.regs 3).toNat % 2 ^ 32) = 100 ∨ ((S0.regs 3).toNat % 2 ^ 32) = 115 ∨ ((S0.regs 3).toNat % 2 ^ 32) = 118
                · have k : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x144)) S7
                      (fun S => FInv rt stack z tab data ((S0.regs 3).toNat % 2 ^ 32) S0 S ∧ (∃ r3 j1, PlainHist RW RP RF data fW fP fF r3 j1) ∧
                        (((S0.regs 3).toNat % 2 ^ 32) = 100 ∨ ((S0.regs 3).toNat % 2 ^ 32) = 115 ∨ ((S0.regs 3).toNat % 2 ^ 32) = 118)) :=
                    rr_mono (sw_dec impl rt stack fW fP fF fWr z tab data ((S0.regs 3).toNat % 2 ^ 32) S0 S7 hr7 hpre hi7 hlt hdec) (fun S h => ⟨h, hpl, hdec⟩)
                  refine RT.widen (RT.of_reachesRet k) ?_
                  intro t ht; simp only [List.mem_singleton] at ht; subst ht
                  exact ⟨_, List.mem_cons_self .., rfl, fun _ h => h⟩
                · by_cases hhex : ((S0.regs 3).toNat % 2 ^ 32) = 120
                  · have k : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x19c)) S7
                        (fun S => FInv rt stack z tab data ((S0.regs 3).toNat % 2 ^ 32) S0 S ∧ (∃ r3 j1, PlainHist RW RP RF data fW fP fF r3 j1) ∧ ((S0.regs 3).toNat % 2 ^ 32) = 120) :=
                      rr_mono (sw_hex impl rt stack fW fP fF fWr z tab data ((S0.regs 3).toNat % 2 ^ 32) S0 S7 hr7 hpre hi7 hlt hhex) (fun S h => ⟨h, hpl, hhex⟩)
                    refine RT.widen (RT.of_reachesRet k) ?_
                    intro t ht; simp only [List.mem_singleton] at ht; subst ht
                    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, fun _ h => h⟩
                  · have k : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x204)) S7
                        (fun S => FInv rt stack z tab data ((S0.regs 3).toNat % 2 ^ 32) S0 S ∧ NotPlain RW RP RF data fW fP fF (S0.regs 3) ((S0.regs 3).toNat % 2 ^ 32)) :=
                      rr_mono (sw_big impl rt stack fW fP fF fWr z tab data ((S0.regs 3).toNat % 2 ^ 32) S0 S7 hr7 hpre hi7 hlt (fun h => hdec (Or.inl h))
                        (fun h => hdec (Or.inr (Or.inl h))) (fun h => hdec (Or.inr (Or.inr h))) hhex)
                        (fun S h => ⟨h, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨j1w, hH7, fun h => hdec (Or.inl h), fun h => hdec (Or.inr (Or.inl h)), fun h => hdec (Or.inr (Or.inr h)), hhex⟩)))))))⟩)
                    refine RT.widen (RT.of_reachesRet k) ?_
                    intro t ht; simp only [List.mem_singleton] at ht; subst ht
                    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), rfl, fun _ h => h⟩
              · obtain ⟨hib, hHb, j0, j1, j2, hR, hb⟩ := hq7
                exact RT.here (Extracted.entry + 0x204, _) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) hr7 ⟨hib, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨j1w, hHb, ⟨_, j0, j1, j2, hR, hb⟩⟩)))))))⟩
            · obtain ⟨hib, hHb, j0, j1, j2, hR, hb⟩ := hq6
              exact RT.here (Extracted.entry + 0x204, _) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) hr6 ⟨hib, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨j1w, hHb, ⟨_, j0, j1, j2, hR, hb⟩⟩))))))⟩
          · obtain ⟨hib, hHb, j0, j1, j2, hR, hb⟩ := hq5
            exact RT.here (Extracted.entry + 0x204, _) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) hr5 ⟨hib, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨j1w, hHb, ⟨_, j0, j1, j2, hR, hb⟩⟩)))))⟩
        · obtain ⟨hib, hHb, j0, j1, j2, hR, hb⟩ := hq4
          exact RT.here (Extracted.entry + 0x204, _) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) hr4 ⟨hib, Or.inr (Or.inr (Or.inr (Or.inl (⟨j1w, hHb, ⟨_, j0, j1, j2, hR, hb⟩⟩))))⟩
      · obtain ⟨hib, hHb, j0, j1, j2, hR, hb⟩ := hq3
        exact RT.here (Extracted.entry + 0x204, _) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) hr3 ⟨hib, Or.inr (Or.inr (Or.inl (⟨j1w, hHb, ⟨_, j0, j1, j2, hR, hb⟩⟩)))⟩
    · obtain ⟨hib, hHb, j0, j1, j2, hR, hb⟩ := hq2
      exact RT.here (Extracted.entry + 0x204, _) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) hr2 ⟨hib, Or.inr (Or.inl (⟨j1w, hHb, ⟨_, _, j0, j1, j2, hR, hb⟩⟩))⟩
  · obtain ⟨hib, -, j0, j1, j2, hRb, hbb⟩ := hq1
    exact RT.here (Extracted.entry + 0x204, _) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) hr1 ⟨hib, Or.inl (⟨j1, ⟨j0, j2, hRb⟩, hbb⟩)⟩

end Fv256.Arm64.FormatFast
