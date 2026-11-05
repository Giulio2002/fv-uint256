import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB

/-!
# arm64 shift expressions of `uint256.udivrem` (Go's `x << s` / `x >> (64-s)` with the `s >= 64 -> 0` guards)

Extraction independent.
-/

namespace Fv256.Arm64.Shift

/-- `(x << s) | (y >> (64 - s))` as the arm64 code computes it (the right shift amount is `128 - (s + 64)`,
guarded by `< 64`), equals the funnel shift. -/
theorem dn_val (x y s : Nat) (hs : s ≤ 63) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    ((if 18446744073709551552 - s - 18446744073709551488 < 64 then
        BitVec.ofNat 64 y >>> ((18446744073709551552 - s - 18446744073709551488) % 64) else 0#64).toNat |||
      (if s < 64 then BitVec.ofNat 64 (x * 2 ^ (s % 64)) else 0#64).toNat) =
      (x * 2 ^ s) % 2 ^ 64 + y / 2 ^ (64 - s) := by
  have hs64 : s % 64 = s := Nat.mod_eq_of_lt (by omega)
  by_cases h0 : s = 0
  · subst h0
    simp only [Nat.sub_zero, Nat.reducePow, Nat.pow_zero, Nat.mul_one]
    rw [if_neg (by omega), if_pos (by omega)]
    simp only [BitVec.toNat_ofNat]
    have : y / 18446744073709551616 = 0 := Nat.div_eq_of_lt (by simpa using hy)
    simp [this, Nat.mod_eq_of_lt hx]
  · have e : 18446744073709551552 - s - 18446744073709551488 = 64 - s := by omega
    rw [e, if_pos (by omega), if_pos (by omega), hs64]
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt (by omega : 64 - s < 64)]
    have e64 : 2 ^ 64 = 2 ^ s * 2 ^ (64 - s) := by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
    have h1 : (x * 2 ^ s) % 2 ^ 64 = (x % 2 ^ (64 - s)) * 2 ^ s := by
      rw [e64, Nat.mul_comm x, Nat.mul_mod_mul_left, Nat.mul_comm]
    have h2 : y / 2 ^ (64 - s) < 2 ^ s := by
      apply Nat.div_lt_of_lt_mul
      rw [Nat.mul_comm, ← e64]; exact hy
    rw [h1, Fv256.Util.or_hi _ _ _ h2]
    omega

end Fv256.Arm64.Shift
