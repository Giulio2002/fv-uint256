import Fv256.Proofs.Common.DecProg
import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.UtilE
import Fv256.Proofs.Amd64.DecA

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Dec

theorem pow100 (j : Nat) : (100:Nat) ^ j = 10 ^ (2 * j) := by
  rw [Nat.pow_mul]

theorem dig_lo (x0 j : Nat) : x0 / 100 ^ j % 100 % 10 = x0 / 10 ^ (2 * j) % 10 := by
  rw [pow100]; generalize x0 / 10 ^ (2 * j) = a; omega

theorem dig_hi (x0 j : Nat) : x0 / 100 ^ j % 100 / 10 = x0 / 10 ^ (2 * j + 1) % 10 := by
  rw [pow100, Nat.pow_succ, ← Nat.div_div_eq_div_mul]; generalize x0 / 10 ^ (2 * j) = a; omega

set_option maxHeartbeats 8000000 in
/-- The 4-iteration inner loop of `formatBase10` (head at `fb+0x60`, exit at `fb+0xbe`): writes the low 8 decimal digits of
`x0` (as zero padded digit pairs) below position `i0`. -/
theorem inner_loop (s0 : State) (ptr len x0 i0 : Nat) (hi : 8 ≤ i0) (hil : i0 ≤ len) (hlo : x0 < 10 ^ 9)
    (hp : ptr + len ≤ 2 ^ 48) :
    ∀ r j (R : Nat → W64) (fl : Flags) (M : Memory), j + r = 4 →
      M.accessible ptr len true = true → TabsOK M →
      R 0 = BitVec.ofNat 64 j → R 3 = BitVec.ofNat 64 (i0 - 2 * j) → R 1 = BitVec.ofNat 64 len →
      R 7 = BitVec.ofNat 64 ptr → R 6 = BitVec.ofNat 64 (x0 / 100 ^ j) →
      ReachesRet Fv256.DecProg.program (BitVec.ofNat 64 (fb + 0xbe))
        { s0 with regs := R, rip := BitVec.ofNat 64 (fb + 0x60), flags := fl, mem := M }
        (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
          S' = { s0 with regs := R', rip := BitVec.ofNat 64 (fb + 0xbe), flags := fl', mem := M' } ∧
          R' 0 = BitVec.ofNat 64 4 ∧ R' 3 = BitVec.ofNat 64 (i0 - 8) ∧ R' 6 = BitVec.ofNat 64 (x0 / 10 ^ 8) ∧
          (∀ k, k ∉ [0, 3, 6, 8, 9, 10, 11] → R' k = R k) ∧
          (∀ k, 2 * j ≤ k → k < 8 → M'.readLE (ptr + i0 - 1 - k) 1 = 48 + x0 / 10 ^ k % 10) ∧
          MemFrame M M' [(ptr + i0 - 8, ptr + i0 - 2 * j)] ∧ TabsOK M') := by
  intro r
  induction r with
  | zero =>
    intro j R fl M hj hacc hd e0 e3 e1 e7 e6
    have hj4 : j = 4 := by omega
    subst hj4
    have hc : fb + 0x300 < 2 ^ 47 := by decide
    janus64_run [e0, e3, e1, e7, e6]
    refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, hd⟩
    · simp [e0]
    · simp [e3]
    · simp [e6]
    · intro k hk; rfl
    · intro k h1 h2; omega
    · exact MemFrame.refl _ _
  | succ r ih =>
    intro j R fl M hj hacc hd e0 e3 e1 e7 e6
    have hj4 : j < 4 := by omega
    have hx : x0 / 100 ^ j < 10 ^ 9 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlo
    have hij : 2 ≤ i0 - 2 * j := by omega
    refine Fv256.E.reachesRet_bind (inner_step s0 ptr len (x0 / 100 ^ j) (i0 - 2 * j) j R fl M hj4 hij (by omega) hx hp hacc
      e0 e3 e1 e7 e6 hd) ?_
    rintro S ⟨R', fl', M', rfl, f0, f3, f6, fk, fr1, fr2, fm, fd⟩
    have hacc' : M'.accessible ptr len true = true := by rw [fm.accessible]; exact hacc
    have hdiv : x0 / 100 ^ j / 100 = x0 / 100 ^ (j + 1) := by rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
    have e1' : R' 1 = BitVec.ofNat 64 len := by rw [fk 1 (by simp), e1]
    have e7' : R' 7 = BitVec.ofNat 64 ptr := by rw [fk 7 (by simp), e7]
    have e3' : R' 3 = BitVec.ofNat 64 (i0 - 2 * (j + 1)) := by rw [f3]; congr 1
    have e6' : R' 6 = BitVec.ofNat 64 (x0 / 100 ^ (j + 1)) := by rw [f6, hdiv]
    refine ReachesRet.mono (ih (j + 1) R' fl' M' (by omega) hacc' fd f0 e3' e1' e7' e6') ?_
    rintro S ⟨R'', fl'', M'', rfl, g0, g3, g6, gk, gr, gm, gd⟩
    refine ⟨R'', fl'', M'', rfl, g0, g3, g6, ?_, ?_, ?_, gd⟩
    · intro k hk
      rw [gk k hk, fk k hk]
    · intro k h1 h2
      by_cases hk2 : k < 2 * j + 2
      · have hout : Outside (ptr + i0 - 1 - k) 1 [(ptr + i0 - 8, ptr + i0 - 2 * (j + 1))] := by
          simp only [Outside, outside_nil, and_true]; omega
        rw [gm.readLE _ _ hout]
        have ha1 : ptr + (i0 - 2 * j) - 1 = ptr + i0 - 1 - 2 * j := by omega
        have ha2 : ptr + (i0 - 2 * j) - 2 = ptr + i0 - 1 - (2 * j + 1) := by omega
        rw [ha1, dig_lo] at fr2
        rw [ha2, dig_hi] at fr1
        by_cases hk0 : k = 2 * j
        · subst hk0; exact fr2
        · have hk1 : k = 2 * j + 1 := by omega
          subst hk1; exact fr1
      · exact gr k (by omega) h2
    · refine fm.trans gm ?_
      intro a n h
      simp only [Outside, outside_nil, and_true] at h ⊢
      omega
end Fv256.Amd64.Dec
