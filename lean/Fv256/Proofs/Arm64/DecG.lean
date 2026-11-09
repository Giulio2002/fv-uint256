import Fv256.Proofs.Arm64.DecProg
import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.UtilE
import Fv256.Proofs.Common.UtilE64
import Fv256.Proofs.Common.DecMath
import Fv256.Proofs.Arm64.DecT
import Fv256.Proofs.Arm64.DecA
import Fv256.Proofs.Arm64.DecF

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI
open Fv256.E

namespace Fv256.Arm64.Dec

theorem dig_div100 (u c : Nat) : u / 10 ^ c / 100 = u / 10 ^ (c + 2) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_add]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem fin_loop (ptr len u0 i0 : Nat) (hu : u0 < 2 ^ 29) (hdl : decLen u0 ≤ i0) (hil : i0 ≤ len)
    (hp : ptr + len ≤ 2 ^ 48) :
    ∀ lo c (s : State), lo = u0 / 10 ^ c → c + decLen lo ≤ i0 →
      s.mem.accessible ptr len true = true → TabsOK s.mem → s.pc = BitVec.ofNat 64 (fb + 0x118) →
      s.regs 0 = BitVec.ofNat 64 ptr → s.regs 2 = BitVec.ofNat 64 len → s.regs 1 = BitVec.ofNat 64 (i0 - c) →
      s.regs 3 = BitVec.ofNat 64 lo →
      (∀ k, k < c → s.mem.readLE (ptr + i0 - 1 - k) 1 = 48 + u0 / 10 ^ k % 10) →
      ReachesRet Fv256.Arm64.DecProg.program (BitVec.ofNat 64 (fb + 0x17c)) s (fun S' => ∃ c' : Nat,
        c ≤ c' ∧ (c' = c ∨ 1 ≤ u0 / 10 ^ c') ∧ c' + decLen (u0 / 10 ^ c') ≤ i0 ∧ u0 / 10 ^ c' < 100 ∧
        S'.regs 0 = BitVec.ofNat 64 ptr ∧ S'.regs 2 = BitVec.ofNat 64 len ∧ S'.regs 1 = BitVec.ofNat 64 (i0 - c') ∧
        S'.regs 3 = BitVec.ofNat 64 (u0 / 10 ^ c') ∧
        (∀ k, k ∉ [1, 3, 4, 5, 6, 7, 8, 9, 10, 11] → S'.regs k = s.regs k) ∧ S'.sp = s.sp ∧
        (∀ k, k < c' → S'.mem.readLE (ptr + i0 - 1 - k) 1 = 48 + u0 / 10 ^ k % 10) ∧
        MemFrame s.mem S'.mem [(ptr + i0 - c', ptr + i0 - c)] ∧ TabsOK S'.mem) := by
  intro lo
  induction lo using Nat.strongRecOn with
  | _ lo ih =>
    intro c s hlo hdc hacc hd hpc e0 e2 e1 e3 hw
    have hc : fb + 0x300 < 2 ^ 47 := by decide
    have hlenlo : lo < 10 ^ decLen lo := decLen_lt_pow lo
    by_cases hlt : lo < 100
    · have hsw : (BitVec.setWidth 32 (BitVec.ofNat 64 lo)).toNat = lo := by
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : lo < 2 ^ 64), Nat.mod_eq_of_lt (by omega : lo < 2 ^ 32)]
      janus_run [hsw, e3] until [fb + 0x17c]
      refine ReachesRet.done (by rfl) ⟨c, Nat.le_refl _, Or.inl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← hlo]; exact hdc
      · rw [← hlo]; exact hlt
      · simpa using e0
      · simpa using e2
      · simpa using e1
      · simpa [hlo] using e3
      · intro k hk; rfl
      · trivial
      · simpa using hw
      · exact MemFrame.refl _ _
      · simpa using hd
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
      refine reachesRet64_bind (fin_step s ptr len lo (i0 - c) hge hlo29 hi2 hia hp hacc hd hpc e0 e2 e1 e3) ?_
      rintro S hpc1 ⟨a0, a2, a1, a3, ak, asp, am1, am2, afr, ad⟩
      have hacc1 : S.mem.accessible ptr len true = true := by rw [afr.accessible]; exact hacc
      have hlo' : lo / 100 = u0 / 10 ^ (c + 2) := by rw [hlo]; exact dig_div100 u0 c
      have hdc' : c + 2 + decLen (lo / 100) ≤ i0 := by omega
      have hw1 : ∀ k, k < c + 2 → S.mem.readLE (ptr + i0 - 1 - k) 1 = 48 + u0 / 10 ^ k % 10 := by
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
      refine reachesRet64_mono (ih (lo / 100) (by omega) (c + 2) S hlo' hdc' hacc1 ad hpc1 a0 a2
        (by rw [a1]; congr 1) a3 hw1) ?_
      rintro S2 ⟨c', b1, bz, b2, b3, b4, b5, b6, b7, b8, bsp, b9, b10, b11⟩
      have hz : 1 ≤ u0 / 10 ^ c' := by
        rcases bz with h | h
        · rw [h, ← hlo']; omega
        · exact h
      refine ⟨c', by omega, Or.inr hz, b2, b3, b4, b5, b6, b7, ?_, ?_, b9, ?_, b11⟩
      · intro k hk
        rw [b8 k hk, ak k hk]
      · rw [bsp, asp]
      · refine afr.trans b10 ?_
        intro a n h
        simp only [Outside, and_true] at h ⊢
        omega
end Fv256.Arm64.Dec
