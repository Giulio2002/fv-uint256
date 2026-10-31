import Fv256.SpecC
import Fv256.Util

namespace Fv256.C

theorem bigAbs_mod_aux (w : Nat → Nat) (k : Nat) :
    bigAbs w (4 + k) % 2 ^ 256 = bigAbs w 4 % 2 ^ 256 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (bigAbs w (4 + k) + w (4 + k) * 2 ^ (64 * (4 + k))) % 2 ^ 256 = _
    have : 2 ^ (64 * (4 + k)) = 2 ^ 256 * 2 ^ (64 * k) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [this, show w (4 + k) * (2 ^ 256 * 2 ^ (64 * k)) = 2 ^ 256 * (w (4 + k) * 2 ^ (64 * k)) by rw [Nat.mul_left_comm],
      Nat.add_mul_mod_self_left]
    exact ih

theorem bigAbs_mod (w : Nat → Nat) (n : Nat) (h : 4 ≤ n) :
    bigAbs w n % 2 ^ 256 = bigAbs w 4 % 2 ^ 256 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 + k := ⟨n - 4, by omega⟩
  exact bigAbs_mod_aux w k

end Fv256.C
