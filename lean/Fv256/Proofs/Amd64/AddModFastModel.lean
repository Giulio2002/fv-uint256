import Fv256.Proofs.Common.UtilF
namespace Fv256.F
def fastModel (x y m : Nat) : Nat :=
  let X := if x < m then x else (x + 2 ^ 256 - m) % 2 ^ 256
  let Y := if y < m then y else (y + 2 ^ 256 - m) % 2 ^ 256
  let r := (X + Y) % 2 ^ 256
  let c := (X + Y) / 2 ^ 256
  if c = 0 ∧ r < m then r else (r + 2 ^ 256 - m) % 2 ^ 256

theorem fm_red (x m : Nat) (hx : x < 2 ^ 256) (hm : 2 ^ 192 ≤ m) (hm2 : m < 2 ^ 256)
    (hxm : x < m + 2 ^ 192) :
    ∃ X k, X < m ∧ k ≤ 1 ∧ x = X + k * m ∧ (if x < m then x else (x + 2 ^ 256 - m) % 2 ^ 256) = X := by
  by_cases h : x < m
  · exact ⟨x, 0, h, by omega, by omega, by simp [h]⟩
  · refine ⟨x - m, 1, by omega, by omega, by omega, ?_⟩
    rw [ite_cond_eq_false _ _ (by simpa using h)]; omega

theorem fastModel_eq (x y m : Nat) (hx : x < 2 ^ 256) (hy : y < 2 ^ 256) (hm : 2 ^ 192 ≤ m) (hm2 : m < 2 ^ 256)
    (hxm : x < m + 2 ^ 192) (hym : y < m + 2 ^ 192) : fastModel x y m = (x + y) % m := by
  obtain ⟨X, a, hX, ha, hxX, e1⟩ := fm_red x m hx hm hm2 hxm
  obtain ⟨Y, b, hY, hb, hyY, e2⟩ := fm_red y m hy hm hm2 hym
  unfold fastModel
  simp only [e1, e2]
  have hs : x + y = X + Y + (a + b) * m := by rw [hxX, hyY, Nat.add_mul]; omega
  by_cases hc : (X + Y) / 2 ^ 256 = 0 ∧ (X + Y) % 2 ^ 256 < m
  · rw [ite_cond_eq_true _ _ (by simpa using hc)]
    have : (X + Y) % 2 ^ 256 = X + Y := by omega
    rw [this]
    exact (mod_dec _ _ _ (a + b) hs (by omega)).symm
  · rw [ite_cond_eq_false _ _ (by simpa using hc)]
    have h2 : ((X + Y) % 2 ^ 256 + 2 ^ 256 - m) % 2 ^ 256 = X + Y - m := by omega
    rw [h2]
    refine (mod_dec _ _ _ (a + b + 1) ?_ (by omega)).symm
    rw [hs, Nat.add_mul (a+b) 1]; omega
end Fv256.F
