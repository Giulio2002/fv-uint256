import Fv256.Arm64.SDivProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.Arm64.DivSum
import Fv256.Arm64.SDivLemmas
import Fv256.Arm64.CodeIn

/-! `SDiv` (arm64) summary over the shared library program `SDivProg.program` (Extracted-free); callee `Div` via `DivSum.div_summary`. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SDivSum

set_option maxRecDepth 200000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.DivProg.program Fv256.Arm64.SDivProg.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

abbrev sdivEntry : Nat := segAddr Fv256.Arm64.SDivProg.program "github.com/holiman/uint256.(*Int).SDiv"

namespace Local
open Fv256.B

theorem abs_zero : Fv256.Spec.abs 0 = 0 := by simp [Fv256.Spec.abs]
theorem neg_zero : Fv256.Spec.neg 0 = 0 := by simp [Fv256.Spec.neg, Fv256.Spec.W]

theorem sdivSpec_x0 (x y : Nat) (h : x = 0) : sdivSpec x y = 0 := by
  subst h; unfold sdivSpec; simp [abs_zero, neg_zero, divSpec_zero_left]

theorem sdivSpec_y0 (x y : Nat) (h : y = 0) : sdivSpec x y = 0 := by
  subst h; unfold sdivSpec; simp [abs_zero, neg_zero, divSpec_zero_right]

theorem sdivSpec_zl (y : Nat) : sdivSpec 0 y = 0 := sdivSpec_x0 0 y rfl
theorem sdivSpec_zr (x : Nat) : sdivSpec x 0 = 0 := sdivSpec_y0 x 0 rfl

end Local

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem sdiv_summary : Summary Fv256.Arm64.SDivProg.program sdivEntry
    (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 592 ∧ StackOK s 632 16 ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 632 ∨ s.sp.toNat + 16 ≤ (s.regs 28).toNat + 16) ∧
        (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
        (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
        (s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧
        ((s.regs 0).toNat + 32 ≤ s.sp.toNat - 632 ∨ s.sp.toNat + 16 ≤ (s.regs 0).toNat) ∧
        ((s.regs 1).toNat + 32 ≤ s.sp.toNat - 632 ∨ s.sp.toNat + 16 ≤ (s.regs 1).toNat) ∧
        ((s.regs 2).toNat + 32 ≤ s.sp.toNat - 632 ∨ s.sp.toNat + 16 ≤ (s.regs 2).toNat))
    (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 27] → s'.regs i = s.regs i) ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.B.sdivSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 632, s.sp.toNat - 8),
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
  janus_run [Util.readLE_32, Nat.or_eq_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff] calls [Janus.Contracts.EqHashModel.Summary.of_codeIn hcLib Fv256.Arm64.DivSum.div_summary]
  · -- x = 0
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      repeat' rw [if_neg (by omega)]
    · exact (Local.sdivSpec_zl _).symm
    · janus_frame
  · -- y = 0
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      repeat' rw [if_neg (by omega)]
    · exact (Local.sdivSpec_zr _).symm
    · janus_frame
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
    · rw [Fv256.Arm64.SDivLemmas.sd_pp _ _ (by omega) (by omega)]; exact hval
    · janus_frame
  · -- pos neg
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
    · rw [ny] at hval
      rw [Fv256.Arm64.SDivLemmas.sd_pn _ _ (by omega) (by omega), ← hval]
      exact nz
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
      rw [Fv256.Arm64.SDivLemmas.sd_np _ _ (by omega) (by omega), ← hval]
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
      rw [Fv256.Arm64.SDivLemmas.sd_nn _ _ (by omega) (by omega)]
      exact hval
    · janus_frame

end Fv256.Arm64.SDivSum
