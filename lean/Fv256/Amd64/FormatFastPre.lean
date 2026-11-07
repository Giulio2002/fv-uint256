import Extracted
import Fv256.FormatFastDefs
import Fv256.FormatFastFacts
import Fv256.Amd64.FormatFastW
import Fv256.Amd64.FormatFastSites
import Fv256.Amd64.FormatFastSw

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.IfaceAmd64
open Fv256.FormatFast

namespace Fv256.Amd64.FormatFast

/-- the answers the machine acted on when it left the query chain for the big path (first non-plain answer, or a verb outside `d v s x`) -/
def NotPlain (RW RP RF : Res) (data tab rW : BitVec 64) (fP fF ch : Nat) : Prop :=
  (∃ j3, WRes RW data tab rW j3 ∧ j3.toNat % 256 ≠ 0) ∨
  (∃ j3, (WRes RW data tab rW j3 ∧ j3.toNat % 256 = 0) ∧ PRes RP data j3 fP (fun j => j.toNat % 256 ≠ 0)) ∨
  (∃ j3, ((WRes RW data tab rW j3 ∧ j3.toNat % 256 = 0) ∧ PRes RP data j3 fP (fun j => j.toNat % 256 = 0)) ∧
    FRes RF data fF 0x2b (fun j => j.toNat % 256 ≠ 0)) ∨
  (∃ j3, (((WRes RW data tab rW j3 ∧ j3.toNat % 256 = 0) ∧ PRes RP data j3 fP (fun j => j.toNat % 256 = 0)) ∧
    FRes RF data fF 0x2b fz) ∧ FRes RF data fF 0x20 (fun j => j.toNat % 256 ≠ 0)) ∨
  (∃ j3, ((((WRes RW data tab rW j3 ∧ j3.toNat % 256 = 0) ∧ PRes RP data j3 fP (fun j => j.toNat % 256 = 0)) ∧
    FRes RF data fF 0x2b fz) ∧ FRes RF data fF 0x20 fz) ∧ FRes RF data fF 0x2d (fun j => j.toNat % 256 = 1)) ∨
  (∃ j3, (((((WRes RW data tab rW j3 ∧ j3.toNat % 256 = 0) ∧ PRes RP data j3 fP (fun j => j.toNat % 256 = 0)) ∧
    FRes RF data fF 0x2b fz) ∧ FRes RF data fF 0x20 fz) ∧ FRes RF data fF 0x2d fx) ∧
    FRes RF data fF 0x30 (fun j => j.toNat % 256 ≠ 0)) ∨
  (∃ j3, ((((((WRes RW data tab rW j3 ∧ j3.toNat % 256 = 0) ∧ PRes RP data j3 fP (fun j => j.toNat % 256 = 0)) ∧
    FRes RF data fF 0x2b fz) ∧ FRes RF data fF 0x20 fz) ∧ FRes RF data fF 0x2d fx) ∧ FRes RF data fF 0x30 fz) ∧
    FRes RF data fF 0x23 (fun j => j.toNat % 256 = 1)) ∨
  (∃ j3, PlainHist RW RP RF data tab rW j3 fP fF ∧ ch ≠ 100 ∧ ch ≠ 115 ∧ ch ≠ 118 ∧ ch ≠ 120)

theorem pre_fast (impl : List Amd64.Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RW RP RF : Res)
    (z tab data : BitVec 64)
    (hW : ICallContract64 (Extracted.program.link impl) fW 1 stack 80 rt (fun _ => []) RW (fun _ => True) (RtPreserves64 R2))
    (hP : ICallContract64 (Extracted.program.link impl) fP 1 stack 80 rt (fun _ => []) RP (fun _ => True) (RtPreserves64 R2))
    (hF : ICallContract64 (Extracted.program.link impl) fF 2 stack 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2))
    (S0 : State) (hpc : S0.rip = BitVec.ofNat 64 (Extracted.entry + 0x45))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0)
    (hwR : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) R2.rt) :
    RT (Extracted.program.link impl) S0
      [(Extracted.entry + 0x139, fun S => FInv rt stack z tab data ((S0.regs 7).toNat % 2 ^ 32) S0 S ∧
          (∃ j3, PlainHist RW RP RF data tab (S0.regs 7) j3 fP fF) ∧
          ((S0.regs 7).toNat % 2 ^ 32 = 100 ∨ (S0.regs 7).toNat % 2 ^ 32 = 115 ∨ (S0.regs 7).toNat % 2 ^ 32 = 118)),
       (Extracted.entry + 0x176, fun S => FInv rt stack z tab data ((S0.regs 7).toNat % 2 ^ 32) S0 S ∧
          (∃ j3, PlainHist RW RP RF data tab (S0.regs 7) j3 fP fF) ∧ (S0.regs 7).toNat % 2 ^ 32 = 120),
       (Extracted.entry + 0x1cc, fun S => FInv rt stack z tab data ((S0.regs 7).toNat % 2 ^ 32) S0 S ∧ RPres R2 S0 S ∧
          NotPlain RW RP RF data tab (S0.regs 7) fP fF ((S0.regs 7).toNat % 2 ^ 32))] := by
  have hlt : (S0.regs 7).toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)

  refine RT.trans (w_site impl R2 rt stack fW fP fF fWr RW z tab data hW S0 hpc hpre hwR) ?_
  intro t ht S1 hr1 hq1
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · obtain ⟨hi1, hk1, j0, j3, j1, hR1, h31, hb1⟩ := hq1
    have hH1 : WRes RW data tab (S0.regs 7) j3 ∧ j3.toNat % 256 = 0 := ⟨⟨j0, j1, hR1⟩, hb1⟩
    refine RT.trans (p_site impl R2 rt stack fW fP fF fWr RP z tab data ((S0.regs 7).toNat % 2 ^ 32) _ hH1 hP S0 S1 hr1 hpre hi1 hk1 hwR j3 h31) ?_
    intro t ht S2 hr2 hq2
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · obtain ⟨hi2, hk2, hHa2, hR2⟩ := hq2
      have hH2 := And.intro hHa2 hR2
      refine RT.trans (f1_site impl R2 rt stack fW fP fF fWr RF z tab data ((S0.regs 7).toNat % 2 ^ 32) _ hH2 hF S0 S2 hr2 hpre hi2 hk2 hwR) ?_
      intro t ht S3 hr3 hq3
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · obtain ⟨hi3, hk3, hHa3, hR3⟩ := hq3
        have hH3 := And.intro hHa3 hR3
        refine RT.trans (f2_site impl R2 rt stack fW fP fF fWr RF z tab data ((S0.regs 7).toNat % 2 ^ 32) _ hH3 hF S0 S3 hr3 hpre hi3 hk3 hwR) ?_
        intro t ht S4 hr4 hq4
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · obtain ⟨hi4, hk4, hHa4, hR4⟩ := hq4
          have hH4 := And.intro hHa4 hR4
          refine RT.trans (f3_site impl R2 rt stack fW fP fF fWr RF z tab data ((S0.regs 7).toNat % 2 ^ 32) _ hH4 hF S0 S4 hr4 hpre hi4 hk4 hwR) ?_
          intro t ht S5 hr5 hq5
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · obtain ⟨hi5, hk5, hHa5, hR5⟩ := hq5
            have hH5 := And.intro hHa5 hR5
            refine RT.trans (f4_site impl R2 rt stack fW fP fF fWr RF z tab data ((S0.regs 7).toNat % 2 ^ 32) _ hH5 hF S0 S5 hr5 hpre hi5 hk5 hwR) ?_
            intro t ht S6 hr6 hq6
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
            rcases ht with rfl | rfl
            · obtain ⟨hi6, hk6, hHa6, hR6⟩ := hq6
              have hH6 := And.intro hHa6 hR6
              refine RT.trans (f5_site impl R2 rt stack fW fP fF fWr RF z tab data ((S0.regs 7).toNat % 2 ^ 32) _ hH6 hF S0 S6 hr6 hpre hi6 hk6 hwR) ?_
              intro t ht S7 hr7 hq7
              simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
              rcases ht with rfl | rfl
              · obtain ⟨hi7, hk7, hHa7, hR7⟩ := hq7
                have hH7 := And.intro hHa7 hR7
                have hpl : ∃ j3, PlainHist RW RP RF data tab (S0.regs 7) j3 fP fF := ⟨j3, hH7⟩
                by_cases hdec : ((S0.regs 7).toNat % 2 ^ 32) = 100 ∨ ((S0.regs 7).toNat % 2 ^ 32) = 115 ∨ ((S0.regs 7).toNat % 2 ^ 32) = 118
                · have k : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x139)) S7
                      (fun S => FInv rt stack z tab data ((S0.regs 7).toNat % 2 ^ 32) S0 S ∧ (∃ j3, PlainHist RW RP RF data tab (S0.regs 7) j3 fP fF) ∧
                        (((S0.regs 7).toNat % 2 ^ 32) = 100 ∨ ((S0.regs 7).toNat % 2 ^ 32) = 115 ∨ ((S0.regs 7).toNat % 2 ^ 32) = 118)) :=
                    ReachesRet.mono (sw_dec impl rt stack fW fP fF fWr z tab data ((S0.regs 7).toNat % 2 ^ 32) S0 S7 hr7 hpre hi7 hlt hdec) (fun S h => ⟨h, hpl, hdec⟩)
                  refine RT.widen (RT.of_reachesRet k) ?_
                  intro t ht; simp only [List.mem_singleton] at ht; subst ht
                  exact ⟨_, List.mem_cons_self .., rfl, fun _ h => h⟩
                · by_cases hhex : ((S0.regs 7).toNat % 2 ^ 32) = 120
                  · have k : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x176)) S7
                        (fun S => FInv rt stack z tab data ((S0.regs 7).toNat % 2 ^ 32) S0 S ∧ (∃ j3, PlainHist RW RP RF data tab (S0.regs 7) j3 fP fF) ∧
                          ((S0.regs 7).toNat % 2 ^ 32) = 120) :=
                      ReachesRet.mono (sw_hex impl rt stack fW fP fF fWr z tab data ((S0.regs 7).toNat % 2 ^ 32) S0 S7 hr7 hpre hi7 hlt hhex) (fun S h => ⟨h, hpl, hhex⟩)
                    refine RT.widen (RT.of_reachesRet k) ?_
                    intro t ht; simp only [List.mem_singleton] at ht; subst ht
                    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, fun _ h => h⟩
                  · have k : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1cc)) S7
                        (fun S => FInv rt stack z tab data ((S0.regs 7).toNat % 2 ^ 32) S0 S ∧ RPres R2 S0 S ∧ NotPlain RW RP RF data tab (S0.regs 7) fP fF ((S0.regs 7).toNat % 2 ^ 32)) :=
                      ReachesRet.mono (sw_big impl rt stack fW fP fF fWr z tab data ((S0.regs 7).toNat % 2 ^ 32) S0 S7 hr7 hpre hi7 hlt (fun h => hdec (Or.inl h))
                        (fun h => hdec (Or.inr (Or.inl h))) (fun h => hdec (Or.inr (Or.inr h))) hhex)
                        (fun S h => ⟨h.1, hk7.trans (RPres.of_mem h.2) hi7.2.2.1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨j3, hH7, fun h => hdec (Or.inl h), fun h => hdec (Or.inr (Or.inl h)), fun h => hdec (Or.inr (Or.inr h)), hhex⟩)))))))⟩)
                    refine RT.widen (RT.of_reachesRet k) ?_
                    intro t ht; simp only [List.mem_singleton] at ht; subst ht
                    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), rfl, fun _ h => h⟩
              · obtain ⟨hib, hkb, hHb, hRb⟩ := hq7
                refine RT.here (Extracted.entry + 0x1cc, _) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) hr7 ⟨hib, hkb, ?_⟩
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨j3, hHb, hRb⟩)))))))
            · obtain ⟨hib, hkb, hHb, hRb⟩ := hq6
              refine RT.here (Extracted.entry + 0x1cc, _) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) hr6 ⟨hib, hkb, ?_⟩
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨j3, hHb, hRb⟩))))))
          · obtain ⟨hib, hkb, hHb, hRb⟩ := hq5
            refine RT.here (Extracted.entry + 0x1cc, _) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) hr5 ⟨hib, hkb, ?_⟩
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨j3, hHb, hRb⟩)))))
        · obtain ⟨hib, hkb, hHb, hRb⟩ := hq4
          refine RT.here (Extracted.entry + 0x1cc, _) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) hr4 ⟨hib, hkb, ?_⟩
          exact Or.inr (Or.inr (Or.inr (Or.inl (⟨j3, hHb, hRb⟩))))
      · obtain ⟨hib, hkb, hHb, hRb⟩ := hq3
        refine RT.here (Extracted.entry + 0x1cc, _) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) hr3 ⟨hib, hkb, ?_⟩
        exact Or.inr (Or.inr (Or.inl (⟨j3, hHb, hRb⟩)))
    · obtain ⟨hib, hkb, hHb, hRb⟩ := hq2
      refine RT.here (Extracted.entry + 0x1cc, _) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) hr2 ⟨hib, hkb, ?_⟩
      exact Or.inr (Or.inl (⟨j3, hHb, hRb⟩))
  · obtain ⟨hib, hkb, j0, j3, j1, hRb, hbb⟩ := hq1
    refine RT.here (Extracted.entry + 0x1cc, _) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) hr1 ⟨hib, hkb, ?_⟩
    exact Or.inl ⟨j3, ⟨j0, j1, hRb⟩, hbb⟩

end Fv256.Amd64.FormatFast
