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
theorem inner_loop (ptr len x0 i0 : Nat) (hi : 8 ≤ i0) (hil : i0 ≤ len) (hlo : x0 < 10 ^ 9) (hp : ptr + len ≤ 2 ^ 48) :
    ∀ r j (s : State), j + r + 1 = 4 → s.mem.accessible ptr len true = true → TabsOK s.mem →
      s.pc = BitVec.ofNat 64 (fb + 0x78) → s.regs 0 = BitVec.ofNat 64 ptr → s.regs 2 = BitVec.ofNat 64 len →
      s.regs 1 = BitVec.ofNat 64 (i0 - 2 * j) → s.regs 6 = BitVec.ofNat 64 j → s.regs 3 = BitVec.ofNat 64 (x0 / 100 ^ j) →
      ReachesRet Extracted.program (BitVec.ofNat 64 (fb + 0xd4)) s (fun S' =>
        S'.regs 0 = BitVec.ofNat 64 ptr ∧ S'.regs 2 = BitVec.ofNat 64 len ∧ S'.regs 1 = BitVec.ofNat 64 (i0 - 8) ∧
        S'.regs 3 = BitVec.ofNat 64 (x0 / 10 ^ 8) ∧ S'.regs 6 = BitVec.ofNat 64 4 ∧
        (∀ k, k ∉ [1, 3, 6, 7, 8, 9, 10, 11] → S'.regs k = s.regs k) ∧ S'.sp = s.sp ∧
        (∀ k, 2 * j ≤ k → k < 8 → S'.mem.readLE (ptr + i0 - 1 - k) 1 = 48 + x0 / 10 ^ k % 10) ∧
        MemFrame s.mem S'.mem [(ptr + i0 - 8, ptr + i0 - 2 * j)] ∧ TabsOK S'.mem) := by
  intro r
  induction r with
  | zero =>
    intro j s hj hacc hd hpc e0 e2 e1 e6 e3
    have hj3 : j = 3 := by omega
    subst hj3
    have hx : x0 / 100 ^ 3 < 10 ^ 9 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlo
    refine reachesRet64_mono (inner_step s (fb + 0xd4) ptr len (x0 / 100 ^ 3) (i0 - 2 * 3) 3 (Or.inr ⟨rfl, rfl⟩) (by omega)
      (by omega) hx hp hacc hd hpc e0 e2 e1 e6 e3) ?_
    rintro S ⟨a0, a2, a1, a3, a6, ak, asp, am1, am2, afr, atab⟩
    refine ⟨a0, a2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, atab⟩
    · rw [a1]; congr 1
    · rw [a3, Nat.div_div_eq_div_mul]
    · rw [a6]
    · intro k hk; exact ak k (by simpa using hk)
    · exact asp
    · intro k h1 h2
      rcases (by omega : k = 6 ∨ k = 7) with rfl | rfl
      · have := am2
        rw [show ptr + (i0 - 2 * 3) - 1 = ptr + i0 - 1 - 6 by omega, dig_lo] at this
        rw [this]; try omega
      · have := am1
        rw [show ptr + (i0 - 2 * 3) - 2 = ptr + i0 - 1 - 7 by omega, dig_hi] at this
        rw [this]
    · exact afr.mono (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)
  | succ r ih =>
    intro j s hj hacc hd hpc e0 e2 e1 e6 e3
    have hx : x0 / 100 ^ j < 10 ^ 9 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlo
    refine reachesRet64_bind (inner_step s (fb + 0x78) ptr len (x0 / 100 ^ j) (i0 - 2 * j) j (Or.inl ⟨by omega, rfl⟩) (by omega)
      (by omega) hx hp hacc hd hpc e0 e2 e1 e6 e3) ?_
    rintro S hpc' ⟨a0, a2, a1, a3, a6, ak, asp, am1, am2, afr, atab⟩
    have hdiv : x0 / 100 ^ j / 100 = x0 / 100 ^ (j + 1) := by rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
    have hacc' : S.mem.accessible ptr len true = true := by rw [afr.accessible]; exact hacc
    refine reachesRet64_mono (ih (j + 1) S (by omega) hacc' atab hpc' a0 a2 (by rw [a1]; congr 1) a6
      (by rw [a3, hdiv])) ?_
    rintro S2 ⟨b0, b2, b1, b3, b6, bk, bsp, bm, bfr, btab⟩
    refine ⟨b0, b2, b1, b3, b6, ?_, ?_, ?_, ?_, btab⟩
    · intro k hk
      rw [bk k hk, ak k hk]
    · rw [bsp, asp]
    · intro k h1 h2
      by_cases hk : k < 2 * j + 2
      · have hout : Outside (ptr + i0 - 1 - k) 1 [(ptr + i0 - 8, ptr + i0 - 2 * (j + 1))] := by
          simp only [Outside, and_true]; omega
        rw [bfr.readLE _ _ hout]
        have ha1 : ptr + (i0 - 2 * j) - 1 = ptr + i0 - 1 - 2 * j := by omega
        have ha2 : ptr + (i0 - 2 * j) - 2 = ptr + i0 - 1 - (2 * j + 1) := by omega
        rw [ha1, dig_lo] at am2
        rw [ha2, dig_hi] at am1
        by_cases hk0 : k = 2 * j
        · subst hk0; rw [am2]; try omega
        · have hk1 : k = 2 * j + 1 := by omega
          subst hk1; rw [am1]
      · exact bm k (by omega) h2
    · refine MemFrame.trans (rs := [(ptr + i0 - 8, ptr + i0 - 2 * j)]) (rs' := [(ptr + i0 - 8, ptr + i0 - 2 * (j + 1))]) ?_ bfr ?_
      · exact afr.mono (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)
      · intro a n h; simp only [Outside, and_true] at h ⊢; exact ⟨h, by omega⟩
end Fv256.Arm64.Dec
