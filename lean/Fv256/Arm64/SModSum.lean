import Fv256.Arm64.SModProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.Arm64.ModSum
import Fv256.Arm64.SDivLemmas
import Fv256.Arm64.SModLemmas
import Fv256.Arm64.CodeIn

/-! `SMod` (arm64) summary over the shared library program `SModProg.program` (Extracted-free); callee `Mod` via `ModSum.mod_summary`. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SModSum

set_option maxRecDepth 200000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ModProg.program Fv256.Arm64.SModProg.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

abbrev smodEntry : Nat := segAddr Fv256.Arm64.SModProg.program "github.com/holiman/uint256.(*Int).SMod"


set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem smod_summary : Summary Fv256.Arm64.SModProg.program smodEntry
    (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 560 ∧ StackOK s 600 16 ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 600 ∨ s.sp.toNat + 16 ≤ (s.regs 28).toNat + 16) ∧
        (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
        (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
        (s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧
        ((s.regs 0).toNat + 32 ≤ s.sp.toNat - 600 ∨ s.sp.toNat + 16 ≤ (s.regs 0).toNat) ∧
        ((s.regs 1).toNat + 32 ≤ s.sp.toNat - 600 ∨ s.sp.toNat + 16 ≤ (s.regs 1).toNat) ∧
        ((s.regs 2).toNat + 32 ≤ s.sp.toNat - 600 ∨ s.sp.toNat + 16 ≤ (s.regs 2).toNat))
    (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 27] → s'.regs i = s.regs i) ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.B.smodSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 600, s.sp.toNat - 8),
          (s.sp.toNat + 8, s.sp.toNat + 16)]) := by
  intro s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, ⟨hsal, hsb, hsc, hsw⟩, hgw, hzb, hza, hxb, hxa, hyb, hya, hdz, hdx, hdy⟩
  have hx0 := Util.readLE8_lt s.mem (s.regs 1).toNat
  have hx1 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 8)
  have hx2 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 16)
  have hx3 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 24)
  have hy0 := Util.readLE8_lt s.mem (s.regs 2).toNat
  have hy1 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 8)
  have hy2 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 16)
  have hy3 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 24)
  janus_run [Util.readLE_32, Nat.or_eq_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff] calls [Janus.Contracts.EqHashModel.Summary.of_codeIn hcLib Fv256.Arm64.ModSum.mod_summary]
  · -- pos pos
    rename_i hregs hval hmem hb1
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hh := hregs i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      by_cases h30 : i = 30
      · subst h30; simp
      · by_cases h29 : i = 29
        · subst h29; simp
        · rw [hh]
          repeat' rw [if_neg (by omega)]
    · rw [Fv256.Arm64.SModLemmas.sm_pp _ _ (by omega) (by omega)]; exact hval
    · janus_frame
  · -- pos neg
    rename_i hregs hval hmem hb1
    have nx := Fv256.Arm64.SDivLemmas.neg4a _ _ _ _ hx0 hx1 hx2 hx3
    have ny := Fv256.Arm64.SDivLemmas.neg4a _ _ _ _ hy0 hy1 hy2 hy3
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hh := hregs i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      by_cases h30 : i = 30
      · subst h30; simp
      · by_cases h29 : i = 29
        · subst h29; simp
        · rw [hh]
          repeat' rw [if_neg (by omega)]
    · rw [ny] at hval
      rw [Fv256.Arm64.SModLemmas.sm_pn _ _ (by omega) (by omega)]
      exact hval
    · janus_frame
  · -- neg pos
    rename_i hregs hval hmem hb1
    have nx := Fv256.Arm64.SDivLemmas.neg4a _ _ _ _ hx0 hx1 hx2 hx3
    have ny := Fv256.Arm64.SDivLemmas.neg4a _ _ _ _ hy0 hy1 hy2 hy3
    have nz := Fv256.Arm64.SDivLemmas.neg4a (s'.mem.readLE (s.regs 0).toNat 8) (s'.mem.readLE ((s.regs 0).toNat + 8) 8)
      (s'.mem.readLE ((s.regs 0).toNat + 16) 8) (s'.mem.readLE ((s.regs 0).toNat + 24) 8)
      (Util.readLE8_lt s'.mem _) (Util.readLE8_lt s'.mem _) (Util.readLE8_lt s'.mem _) (Util.readLE8_lt s'.mem _)
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hh := hregs i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      by_cases h30 : i = 30
      · subst h30; simp
      · by_cases h29 : i = 29
        · subst h29; simp
        · rw [hh]
          repeat' rw [if_neg (by omega)]
    · rw [nx] at hval
      rw [Fv256.Arm64.SModLemmas.sm_np _ _ (by omega) (by omega), ← hval]
      exact nz
    · janus_frame
  · -- neg neg
    rename_i hregs hval hmem hb1
    have nx := Fv256.Arm64.SDivLemmas.neg4a _ _ _ _ hx0 hx1 hx2 hx3
    have ny := Fv256.Arm64.SDivLemmas.neg4a _ _ _ _ hy0 hy1 hy2 hy3
    have nz := Fv256.Arm64.SDivLemmas.neg4a (s'.mem.readLE (s.regs 0).toNat 8) (s'.mem.readLE ((s.regs 0).toNat + 8) 8)
      (s'.mem.readLE ((s.regs 0).toNat + 16) 8) (s'.mem.readLE ((s.regs 0).toNat + 24) 8)
      (Util.readLE8_lt s'.mem _) (Util.readLE8_lt s'.mem _) (Util.readLE8_lt s'.mem _) (Util.readLE8_lt s'.mem _)
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hh := hregs i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      by_cases h30 : i = 30
      · subst h30; simp
      · by_cases h29 : i = 29
        · subst h29; simp
        · rw [hh]
          repeat' rw [if_neg (by omega)]
    · rw [nx, ny] at hval
      rw [Fv256.Arm64.SModLemmas.sm_nn _ _ (by omega) (by omega), ← hval]
      exact nz
    · janus_frame

end Fv256.Arm64.SModSum
