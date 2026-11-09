import Fv256.Proofs.Common.StrProg
import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.UtilE
import Fv256.Proofs.Amd64.P.A

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E

namespace Fv256.Amd64.P

set_option maxHeartbeats 8000000 in
/-- The last one or two digits of `formatBase10` (`lo < 100`, `fb+0x15a` to `fb+0x199`). -/
theorem fin_last (s0 : State) (ptr len lo i : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hlo : lo < 100) (hi : decLen lo ≤ i) (hil : i ≤ len)
    (hp : ptr + len ≤ 2 ^ 48) (hacc : M.accessible ptr len true = true)
    (e0 : R 0 = BitVec.ofNat 64 ptr) (e3 : R 3 = BitVec.ofNat 64 i) (e1 : R 1 = BitVec.ofNat 64 len)
    (e2 : R 2 = BitVec.ofNat 64 lo) (hd : TabsOK M) :
    ReachesRet Fv256.StrProg.program (BitVec.ofNat 64 (fb + 0x199))
      { s0 with regs := R, rip := BitVec.ofNat 64 (fb + 0x15a), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (fb + 0x199), flags := fl', mem := M' } ∧
        R' 6 = BitVec.ofNat 64 (i - decLen lo) ∧ (∀ k, k ∉ [2, 6, 7, 8] → R' k = R k) ∧
        (∀ k, k < decLen lo → M'.readLE (ptr + i - 1 - k) 1 = 48 + lo / 10 ^ k % 10) ∧
        MemFrame M M' [(ptr + i - decLen lo, ptr + i)] ∧ TabsOK M') := by
  have hc : fb + 0x300 < 2 ^ 47 := by decide
  have hsr := hd.smalls lo hlo
  tabs_data hd [hacc]
  by_cases h10 : lo < 10
  · have hl : decLen lo = 1 := decLen_lt lo h10
    rw [hl] at hi ⊢
    janus64_run [e0, e3, e1, e2] until [fb + 0x199]
    have hw : (i + (18446744073709551615 + ptr) % 18446744073709551616) % 18446744073709551616 = ptr + i - 1 := by omega
    have hk1 : ((lo + lo) % 4294967296 + 1) % 4294967296 + 5176582 = 5176582 + 2 * lo + 1 := by
      omega
    rw [hw, hk1]
    refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [setRegF]; simp; exact Fv256.E.ofNat_sub_ofNat i 1 (by omega) (by omega)
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [setRegF, hk]
    · intro k hk
      have : k = 0 := by omega
      subst this
      rw [show ptr + i - 1 - 0 = ptr + i - 1 by omega, Janus.Arm64.Memory.readLE_writeLE_self, hsr.2]
      simp only [Nat.pow_one, Nat.pow_zero, Nat.div_one]; omega
    · exact MemFrame.of_writeLE M _ (r := (ptr + i - 1, ptr + i)) (List.mem_singleton_self _) (by omega) (by omega)
    · exact TabsOK.writeLE hd (accessible_sub hacc (Or.inr rfl) (by omega) (by omega)) _
  · have hl : decLen lo = 2 := by
      have := decLen_ge lo (by omega)
      have h2 : lo / 10 < 10 := by omega
      rw [this, decLen_lt _ h2]
    rw [hl] at hi ⊢
    janus64_run [e0, e3, e1, e2] until [fb + 0x199]
    have hw0 : (i + (18446744073709551614 + ptr) % 18446744073709551616) % 18446744073709551616 = ptr + i - 2 := by omega
    have hw1 : (i + (18446744073709551615 + ptr) % 18446744073709551616) % 18446744073709551616 = ptr + i - 1 := by omega
    have hk0 : (lo % 4294967296 + lo % 4294967296) % 4294967296 + 5176582 = 5176582 + 2 * lo := by
      omega
    have hk1 : ((lo + lo) % 4294967296 + 1) % 4294967296 + 5176582 = 5176582 + 2 * lo + 1 := by
      omega
    rw [hw0, hw1, hk0, hk1]
    refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [setRegF]; simp; exact Fv256.E.ofNat_sub_ofNat i 2 (by omega) (by omega)
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [setRegF, hk]
    · intro k hk
      have hk2 : k = 0 ∨ k = 1 := by omega
      rcases hk2 with rfl | rfl
      · rw [show ptr + i - 1 - 0 = ptr + i - 1 by omega, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Janus.Arm64.Memory.readLE_writeLE_self, hsr.2]
        simp only [Nat.pow_one, Nat.pow_zero, Nat.div_one]; omega
      · rw [show ptr + i - 1 - 1 = ptr + i - 2 by omega, Janus.Arm64.Memory.readLE_writeLE_self, hsr.1]
        simp only [Nat.pow_one, Nat.pow_zero, Nat.div_one]; omega
    · exact ((MemFrame.refl M [(ptr + i - 2, ptr + i)]).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
        (List.mem_singleton_self _) (by omega) (by omega)
    · exact TabsOK.writeLE (TabsOK.writeLE hd (accessible_sub hacc (Or.inr rfl) (by omega) (by omega)) _)
        (by simp only [Janus.Arm64.Memory.accessible_writeLE]; exact accessible_sub hacc (Or.inr rfl) (by omega) (by omega)) _
end Fv256.Amd64.P
