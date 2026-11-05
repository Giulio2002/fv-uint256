import Extracted
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.DecMath
import Fv256.Arm64.DecT
import Fv256.Arm64.DecA

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI
open Fv256.E

namespace Fv256.Arm64.Dec

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- The last one or two digits of `formatBase10` (`lo < 100`, `fb+0x17c` to `fb+0x1cc`). -/
theorem fin_last (s : State) (ptr len lo i : Nat) (hlo : lo < 100) (hi : decLen lo ≤ i) (hil : i ≤ len)
    (hp : ptr + len ≤ 2 ^ 48) (hacc : s.mem.accessible ptr len true = true) (hd : TabsOK s.mem)
    (hpc : s.pc = BitVec.ofNat 64 (fb + 0x17c)) (e0 : s.regs 0 = BitVec.ofNat 64 ptr) (e2 : s.regs 2 = BitVec.ofNat 64 len)
    (e1 : s.regs 1 = BitVec.ofNat 64 i) (e3 : s.regs 3 = BitVec.ofNat 64 lo) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (fb + 0x1cc)) s (fun S' =>
      S'.regs 0 = BitVec.ofNat 64 ptr ∧ S'.regs 2 = BitVec.ofNat 64 len ∧ S'.regs 1 = BitVec.ofNat 64 (i - decLen lo) ∧
      (∀ k, k ∉ [1, 3, 4, 5, 6] → S'.regs k = s.regs k) ∧ S'.sp = s.sp ∧
      (∀ k, k < decLen lo → S'.mem.readLE (ptr + i - 1 - k) 1 = 48 + lo / 10 ^ k % 10) ∧
      MemFrame s.mem S'.mem [(ptr + i - decLen lo, ptr + i)] ∧ TabsOK S'.mem) := by
  have hc : fb + 0x300 < 2 ^ 47 := by decide
  tabs_data hd [hacc]
  have hsr := hd.sm lo hlo
  have h5 := q5 lo hlo
  have h6 := q6 lo hlo
  have hsw : (BitVec.setWidth 32 (BitVec.ofNat 64 lo)).toNat = lo := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : lo < 2 ^ 64), Nat.mod_eq_of_lt (by omega : lo < 2 ^ 32)]
  by_cases h10 : lo < 10
  · have hl : decLen lo = 1 := decLen_lt _ h10
    rw [hl] at hi ⊢
    janus_run [hsw, e0, e1, e2, e3, h5, h6] until [fb + 0x1cc]
    refine ReachesRet.done (by rfl) ?_
    have hm : 1002589 + (2 * lo + 1) = 1002589 + 2 * lo + 1 := by omega
    have hr1 : s.mem.readLE (1002589 + (2 * lo + 1)) 1 = 48 + lo := by
      rw [hm, hsr.2]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setReg, e0]
    · simp [setReg, e2]
    · simp [setReg]; exact Fv256.E.ofNat_sub_ofNat i 1 (by omega) (by omega)
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [setReg, hk]
    · trivial
    · intro k hk
      have : k = 0 := by omega
      subst this
      rw [show ptr + i - 1 - 0 = ptr + (i - 1) by omega, Janus.Arm64.Memory.readLE_writeLE_self, hr1]
      simp only [Nat.pow_one, Nat.pow_zero, Nat.div_one]; omega
    · exact (MemFrame.refl s.mem _).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)
    · exact hd.writeLE (accessible_sub hacc (Or.inr rfl) (by omega) (by omega)) _
  · have hl : decLen lo = 2 := by
      rw [decLen_ge _ (by omega), decLen_lt _ (by omega)]
    rw [hl] at hi ⊢
    janus_run [hsw, e0, e1, e2, e3, h5, h6] until [fb + 0x1cc]
    refine ReachesRet.done (by rfl) ?_
    have hm0 : 2 * lo % 4294967296 = 2 * lo := Nat.mod_eq_of_lt (by omega)
    simp only [hm0]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setReg, e0]
    · simp [setReg, e2]
    · simp [setReg]; exact Fv256.E.ofNat_sub_ofNat i 2 (by omega) (by omega)
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [setReg, hk]
    · trivial
    · intro k hk
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · rw [show ptr + i - 1 - 0 = ptr + (i - 1) by omega, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Janus.Arm64.Memory.readLE_writeLE_self]
        simp only [Nat.pow_one, Nat.pow_zero, Nat.div_one]
        rw [show 1002589 + (2 * lo + 1) = 1002589 + 2 * lo + 1 by omega, hsr.2]; omega
      · rw [show ptr + i - 1 - 1 = ptr + (i - 2) by omega, Janus.Arm64.Memory.readLE_writeLE_self]
        simp only [Nat.pow_one]
        rw [hsr.1]; omega
    · exact ((MemFrame.refl s.mem _).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
        (List.mem_singleton_self _) (by omega) (by omega)
    · exact hd.two hacc (by omega) (by omega) (by omega) (by omega) _ _
end Fv256.Arm64.Dec
