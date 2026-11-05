import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.Arm64.UdivremFront
import Fv256.Arm64.UdivremA
import Fv256.Arm64.UdivremD
import Fv256.Arm64.UdivremE
import Fv256.Arm64.UdivremF
import Fv256.Arm64.DivLemmas

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.UdivremD

namespace Fv256.Arm64.DivSum

abbrev divEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).Div"

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem div_summary_cond (hKn : KnuthStmt) :
    Summary Extracted.program divEntry
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 416 ∧ StackOK s 456 16 ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 456 ∨ s.sp.toNat + 16 ≤ (s.regs 28).toNat + 16) ∧
        (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
        (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
        (s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧
        ((s.regs 0).toNat + 32 ≤ s.sp.toNat - 456 ∨ s.sp.toNat + 16 ≤ (s.regs 0).toNat) ∧
        ((s.regs 1).toNat + 32 ≤ s.sp.toNat - 456 ∨ s.sp.toNat + 16 ≤ (s.regs 1).toNat) ∧
        ((s.regs 2).toNat + 32 ≤ s.sp.toNat - 456 ∨ s.sp.toNat + 16 ≤ (s.regs 2).toNat))
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 27] → s'.regs i = s.regs i) ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.B.divSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 456, s.sp.toNat - 8),
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
  janus_run [Util.readLE_32, Nat.or_eq_zero_iff, Fv256.B.wv4_eq, Fv256.B.wv_writeLE_outside, Fv256.Arm64.DivLemmas.wv_zero4w, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div] until [divEntry + 0x98, divEntry + 0xf0] calls [Fv256.Arm64.UdivremF.udivrem_nil_L (L := 4) (by decide) (by decide) hKn]
  all_goals (try simp only [Janus.Tactic.sub_flags_c, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Fv256.Arm64.DivLemmas.chain_zero_iff _ _ _ _ _ _ _ _ hx0 hx1 hx2 hx3 hy0 hy1 hy2 hy3] at *)
  · sorry
  · sorry
  · have hy0n : s.mem.readLE (s.regs 2).toNat 8 ≠ 0 := by omega
    janus_run [Util.readLE_32, Nat.or_eq_zero_iff, Fv256.B.wv4_eq, Fv256.B.wv_writeLE_outside, Fv256.Arm64.DivLemmas.wv_zero4w, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div]
    have e2 : (s.mem.readLE (s.regs 2).toNat 8 + 18446744073709551616 * s.mem.readLE ((s.regs 2).toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE ((s.regs 2).toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE ((s.regs 2).toNat + 24) 8) = s.mem.readLE (s.regs 2).toNat 8 := by omega
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      repeat' rw [if_neg (by omega)]
    · rw [e2, Fv256.B.divSpec, if_neg hy0n]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx0)
    · janus_frame
  · have hf := ‹MemFrame _ _ _›
    have hsp1 : (s.sp - 112#64).toNat = s.sp.toNat - 112 := by have := s.sp.isLt; simp [BitVec.toNat_sub]; omega
    have hsp2 : (s.sp - 40#64).toNat = s.sp.toNat - 40 := by have := s.sp.isLt; simp [BitVec.toNat_sub]; omega
    simp only [setReg, hsp1, hsp2, Nat.reduceEqDiff, reduceIte, Nat.reduceAdd, Nat.reduceSub] at hf
    have hz8 : s'.mem.readLE (s.sp.toNat + 8) 8 = (s.regs 0).toNat := by
      rw [hf.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have := (s.regs 0).isLt; simpa using this)
    rw [hz8]
    janus_run [Util.readLE_32, Nat.or_eq_zero_iff, Fv256.B.wv4_eq, Fv256.B.wv_writeLE_outside, Fv256.Arm64.DivLemmas.wv_zero4w, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div]
    have hr := ‹∀ (i : Nat), ¬i ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 27] → s'.regs i = _›
    have hq := ‹Fv256.B.wv s'.mem _ 4 = _›
    simp only [setReg, hsp2, reduceIte, Nat.reduceEqDiff] at hq
    simp (disch := omega) only [Fv256.B.wv_writeLE_outside, Fv256.B.wv4_eq, Util.readLE_32] at hq
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have h := hr i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      rw [h]
      by_cases h30 : i = 30
      · subst h30; simp
      · by_cases h29 : i = 29
        · subst h29; simp
        · simp (disch := omega) only [if_neg]
    · rw [Fv256.B.divSpec]
      split
      · rename_i hz
        rw [hz, Nat.div_zero] at hq
        omega
      · omega
    · trace_state
      sorry
  · sorry

end Fv256.Arm64.DivSum
