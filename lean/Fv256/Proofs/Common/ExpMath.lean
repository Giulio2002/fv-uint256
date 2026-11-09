import Fv256.Proofs.Common.SpecF

/-!
# Arithmetic of the binary exponentiation loops of `Exp` (extraction independent)

One loop iteration: `if word & 1 = 1 then res := res * mult; mult := mult * mult; word := word >> 1`, all modulo `2^256`.
-/

namespace Fv256.F

/-- congruence modulo `2^256` -/
def MEq (a b : Nat) : Prop := a % 2 ^ 256 = b % 2 ^ 256
theorem MEq.refl (a : Nat) : MEq a a := rfl
theorem MEq.trans {a b c : Nat} (h1 : MEq a b) (h2 : MEq b c) : MEq a c := Eq.trans h1 h2
theorem MEq.mul {a b c d : Nat} (h1 : MEq a b) (h2 : MEq c d) : MEq (a * c) (b * d) := by
  unfold MEq at *; rw [Nat.mul_mod, h1, h2, ← Nat.mul_mod]
theorem MEq.pow {a b : Nat} (h : MEq a b) (n : Nat) : MEq (a ^ n) (b ^ n) := by
  unfold MEq at *; rw [Nat.pow_mod, h, ← Nat.pow_mod]
theorem meq_mod (a : Nat) : MEq (a % 2 ^ 256) a := by unfold MEq; rw [Nat.mod_mod]

abbrev W : Nat := 2 ^ 256

/-- One step of the square-and-multiply loop on `(res, mult, word)`. -/
def expStep (st : Nat × Nat × Nat) : Nat × Nat × Nat :=
  ((if st.2.2 % 2 = 1 then st.1 * st.2.1 % W else st.1), st.2.1 * st.2.1 % W, st.2.2 / 2)

/-- `k` steps. -/
def expIter : Nat → Nat × Nat × Nat → Nat × Nat × Nat
  | 0, st => st
  | k + 1, st => expIter k (expStep st)

theorem sq_pow_mod (b m : Nat) : (b * b % W) ^ m % W = b ^ (2 * m) % W := by
  rw [← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul]

/-- After `k` steps from `(r, b, e)` the state is `(r * b^(e mod 2^k), b^(2^k), e / 2^k)` modulo `W`. -/
theorem expIter_eq (k : Nat) : ∀ (r b e : Nat), r < W → b < W →
    expIter k (r, b, e) = (r * b ^ (e % 2 ^ k) % W, b ^ (2 ^ k) % W, e / 2 ^ k) := by
  induction k with
  | zero => intro r b e hr hb; simp [expIter, Nat.mod_one, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hb]
  | succ k ih =>
    intro r b e hr hb
    simp only [expIter]
    have hstep : expStep (r, b, e) = ((if e % 2 = 1 then r * b % W else r), b * b % W, e / 2) := rfl
    rw [hstep]
    have h1 : (if e % 2 = 1 then r * b % W else r) < W := by
      split
      · exact Nat.mod_lt _ (by decide)
      · exact hr
    rw [ih _ _ _ h1 (Nat.mod_lt _ (by decide))]
    have hk : e % 2 ^ (k + 1) = e % 2 + 2 * (e / 2 % 2 ^ k) := by
      rw [Nat.pow_succ', Nat.mod_mul]
    have hd : e / 2 / 2 ^ k = e / 2 ^ (k + 1) := by rw [Nat.pow_succ', Nat.div_div_eq_div_mul]
    rw [hd, hk]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · show _ = _
      simp only
      have hb2 : MEq ((b * b % W) ^ (e / 2 % 2 ^ k)) (b ^ (2 * (e / 2 % 2 ^ k))) :=
        ((meq_mod (b * b)).pow _).trans (by rw [← Nat.pow_two, ← Nat.pow_mul]; exact MEq.refl _)
      have hA : MEq (if e % 2 = 1 then r * b % W else r) (r * b ^ (e % 2)) := by
        have hmod : e % 2 = 0 ∨ e % 2 = 1 := by omega
        rcases hmod with h | h
        · simp [h]; exact MEq.refl _
        · simp [h]; exact meq_mod _
      have := hA.mul hb2
      rw [Nat.pow_add, ← Nat.mul_assoc]
      exact this
    · show _ = _
      simp only
      have h2 : MEq ((b * b % W) ^ 2 ^ k) (b ^ 2 ^ (k + 1)) :=
        ((meq_mod (b * b)).pow _).trans (by rw [← Nat.pow_two, ← Nat.pow_mul, Nat.pow_succ']; exact MEq.refl _)
      exact h2

end Fv256.F
