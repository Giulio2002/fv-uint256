import Extracted
import Fv256.SpecE
import Fv256.UtilE
import Fv256.Amd64.DecA
import Fv256.Amd64.DecF

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E

namespace Fv256.Amd64.Dec

theorem dig_div100 (u c : Nat) : u / 10 ^ c / 100 = u / 10 ^ (c + 2) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_add]

set_option maxHeartbeats 8000000 in
theorem fin_loop (s0 : State) (ptr len u0 i0 : Nat) (hu : u0 < 2 ^ 29) (hdl : decLen u0 ≤ i0) (hil : i0 ≤ len)
    (hp : ptr + len ≤ 2 ^ 48) :
    ∀ lo c (R : Nat → W64) (fl : Flags) (M : Memory), lo = u0 / 10 ^ c → c + decLen lo ≤ i0 →
      M.accessible ptr len true = true → TabsOK M →
      R 0 = BitVec.ofNat 64 ptr → R 3 = BitVec.ofNat 64 (i0 - c) → R 1 = BitVec.ofNat 64 len →
      R 2 = BitVec.ofNat 64 lo →
      (∀ k, k < c → M.readLE (ptr + i0 - 1 - k) 1 = 48 + u0 / 10 ^ k % 10) →
      ReachesRet Extracted.program (BitVec.ofNat 64 (fb + 0x15a))
        { s0 with regs := R, rip := BitVec.ofNat 64 (fb + 0x109), flags := fl, mem := M }
        (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory) (c' : Nat),
          S' = { s0 with regs := R', rip := BitVec.ofNat 64 (fb + 0x15a), flags := fl', mem := M' } ∧
          c ≤ c' ∧ (c' = c ∨ 1 ≤ u0 / 10 ^ c') ∧ c' + decLen (u0 / 10 ^ c') ≤ i0 ∧ u0 / 10 ^ c' < 100 ∧
          R' 0 = BitVec.ofNat 64 ptr ∧ R' 1 = BitVec.ofNat 64 len ∧ R' 3 = BitVec.ofNat 64 (i0 - c') ∧
          R' 2 = BitVec.ofNat 64 (u0 / 10 ^ c') ∧ (∀ k, k ∉ [2, 3, 6, 7, 8, 9] → R' k = R k) ∧
          (∀ k, k < c' → M'.readLE (ptr + i0 - 1 - k) 1 = 48 + u0 / 10 ^ k % 10) ∧
          MemFrame M M' [(ptr + i0 - c', ptr + i0 - c)] ∧ TabsOK M') := by
  intro lo
  induction lo using Nat.strongRecOn with
  | _ lo ih =>
    intro c R fl M hlo hdc hacc hd e0 e3 e1 e2 hw
    have hc : fb + 0x300 < 2 ^ 47 := by decide
    have hlenlo : lo < 10 ^ decLen lo := decLen_lt_pow lo
    by_cases hlt : lo < 100
    · janus64_run [e0, e3, e1, e2]
      refine ⟨_, _, _, c, rfl, Nat.le_refl _, Or.inl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← hlo]; exact hdc
      · rw [← hlo]; exact hlt
      · exact e0
      · exact e1
      · exact e3
      · rw [← hlo]; exact e2
      · intro k hk; rfl
      · exact hw
      · exact MemFrame.refl _ _
      · exact hd
    · have hge : 100 ≤ lo := by omega
      have hdlo : decLen lo = decLen (lo / 100) + 2 := by
        have h1 := decLen_ge lo (by omega)
        have h2 := decLen_ge (lo / 10) (by omega)
        rw [h1, h2]
        rw [Nat.div_div_eq_div_mul]
      have hi2 : 2 ≤ i0 - c := by have := decLen_pos (lo / 100); omega
      have hlo29 : lo < 2 ^ 29 := by
        rw [hlo]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hu
      have hia : i0 - c ≤ len := by omega
      refine Fv256.E.reachesRet_bind (fin_step s0 ptr len lo (i0 - c) R fl M hge hlo29 hi2 hia hp hacc e0 e3 e1 e2 hd) ?_
      rintro S ⟨R1, fl1, M1, rfl, a0, a3, a1, a2, ak, am1, am2, afr, ad⟩
      have hacc1 : M1.accessible ptr len true = true := by rw [afr.accessible]; exact hacc
      have hlo' : lo / 100 = u0 / 10 ^ (c + 2) := by rw [hlo]; exact dig_div100 u0 c
      have hdc' : c + 2 + decLen (lo / 100) ≤ i0 := by omega
      have hw1 : ∀ k, k < c + 2 → M1.readLE (ptr + i0 - 1 - k) 1 = 48 + u0 / 10 ^ k % 10 := by
        intro k hk
        by_cases hkc : k < c
        · have hout : Outside (ptr + i0 - 1 - k) 1 [(ptr + (i0 - c) - 2, ptr + (i0 - c))] := by
            simp only [Outside, and_true]; omega
          rw [afr.readLE _ _ hout, hw k hkc]
        · have hk2 : k = c ∨ k = c + 1 := by omega
          rcases hk2 with rfl | rfl
          · have := am2
            rw [show ptr + (i0 - k) - 1 = ptr + i0 - 1 - k by omega, hlo] at this
            rw [this]
          · have := am1
            rw [show ptr + (i0 - c) - 2 = ptr + i0 - 1 - (c + 1) by omega, hlo] at this
            rw [this]
            have hdd : u0 / 10 ^ (c + 1) = u0 / 10 ^ c / 10 := by
              rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
            rw [hdd]
            try omega
      refine ReachesRet.mono (ih (lo / 100) (by omega) (c + 2) R1 fl1 M1 hlo' hdc' hacc1 ad a0
        (by rw [a3]; congr 1) a1 a2 hw1) ?_
      rintro S ⟨R2, fl2, M2, c', rfl, b1, bz, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩
      have hz : 1 ≤ u0 / 10 ^ c' := by
        rcases bz with h | h
        · rw [h, ← hlo']; omega
        · exact h
      refine ⟨R2, fl2, M2, c', rfl, by omega, Or.inr hz, b2, b3, b4, b5, b6, b7, ?_, b9, ?_, b11⟩
      · intro k hk
        rw [b8 k hk, ak k hk]
      · refine afr.trans b10 ?_
        intro a n h
        simp only [Outside, and_true] at h ⊢
        omega
end Fv256.Amd64.Dec
