import Fv256.Spec.Dec
import Fv256.Spec.PrettyDec
import Fv256.Spec.Hex
import Fv256.Spec.E
import Fv256.Spec.PrettyMath
import Fv256.Spec.C

/-!
# Bridges for the text-output functions

The readable specifications `Spec.dec`, `Spec.hex`, `Spec.prettyDec` (digit lists built from Lean's `Nat.toDigits`) agree with the
implementation-shaped ones: `Fv256.E.decBytes`, `Fv256.C.hexStrBytes` (+ `hexDigits`), `Fv256.E.prettyBytes`.
-/

namespace Fv256.TextBridge

/-- the ASCII code of the digit `d` (`< 16`) -/
def dc (d : Nat) : Nat := if d < 10 then 48 + d else 87 + d

/-- ASCII digits of `n` in base `b`, most significant first (the shape of the recursions in `decBytes` and `hexBytes`) -/
def D (b n : Nat) : List Nat :=
  if b ≤ 1 then [] else if n < b then [dc n] else D b (n / b) ++ [dc (n % b)]
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

theorem D_eq (b n : Nat) (hb : 2 ≤ b) : D b n = if n < b then [dc n] else D b (n / b) ++ [dc (n % b)] := by
  rw [D]; simp [show ¬ b ≤ 1 by omega]

theorem digitChar_toNat (d : Nat) (h : d < 16) : (Nat.digitChar d).toNat = dc d := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 ∨ d = 10 ∨ d = 11 ∨ d = 12 ∨
      d = 13 ∨ d = 14 ∨ d = 15 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem toDigitsCore_eq (b : Nat) (hb : 2 ≤ b) (hb16 : b ≤ 16) :
    ∀ f n acc, n < f → (Nat.toDigitsCore b f n acc).map Char.toNat = D b n ++ acc.map Char.toNat := by
  intro f
  induction f with
  | zero => intro n acc h; omega
  | succ f ih =>
    intro n acc h
    rw [Nat.toDigitsCore]
    have hd : (Nat.digitChar (n % b)).toNat = dc (n % b) := digitChar_toNat _ (by have := Nat.mod_lt n (show b > 0 by omega); omega)
    by_cases h1 : n / b = 0
    · have hn : n < b := (Nat.div_eq_zero_iff_lt (by omega)).1 h1
      have hd2 : n.digitChar.toNat = dc n := by have := hd; rw [Nat.mod_eq_of_lt hn] at this; exact this
      simp only [h1, ite_true, List.map_cons, Nat.mod_eq_of_lt hn, hd2, D_eq b n hb, hn]
      simp
    · have hn : ¬ n < b := fun hh => h1 ((Nat.div_eq_zero_iff_lt (by omega)).2 hh)
      simp only [h1, ite_false]
      rw [ih (n / b) _ (by have := Nat.div_lt_self (show 0 < n by omega) (show 1 < b by omega); omega)]
      rw [D_eq b n hb]
      simp only [hn, ite_false, List.map_cons, hd, List.append_assoc, List.singleton_append]

theorem toDigits_eq (b : Nat) (hb : 2 ≤ b) (hb16 : b ≤ 16) (n : Nat) : (Nat.toDigits b n).map Char.toNat = D b n := by
  have := toDigitsCore_eq b hb hb16 (n + 1) n [] (by omega)
  simpa [Nat.toDigits] using this

theorem D10 (n : Nat) : D 10 n = Fv256.E.decBytes n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [D, Fv256.E.decBytes]
    by_cases h : n < 10
    · simp [h, dc]
    · have : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
      simp [h, ih (n / 10) this, dc, show n % 10 < 10 from Nat.mod_lt _ (by omega)]

/-- `Spec.dec` is `Fv256.E.decBytes` -/
theorem dec_eq (n : Nat) : Fv256.Spec.dec n = Fv256.E.decBytes n := by
  unfold Fv256.Spec.dec; rw [toDigits_eq 10 (by omega) (by omega), D10]

theorem pad3_eq (n : Nat) : Fv256.Spec.pad3 n = Fv256.E.pad3 n := rfl

/-- `Spec.prettyDec` is `Fv256.E.prettyBytes` -/
theorem prettyDec_eq (sep n : Nat) : Fv256.Spec.prettyDec sep n = Fv256.E.prettyBytes sep n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [Fv256.Spec.prettyDec, Fv256.E.prettyBytes]
    by_cases h : n < 1000
    · simp [h, dec_eq]
    · have : n / 1000 < n := Nat.div_lt_self (by omega) (by omega)
      simp [h, ih (n / 1000) this, pad3_eq]


theorem D16_digits : ∀ n v, 1 ≤ n → v < 16 ^ n → (n = 1 ∨ 16 ^ (n - 1) ≤ v) →
    D 16 v = (List.range n).map (fun k => dc (v / 16 ^ (n - 1 - k) % 16)) := by
  intro n
  induction n with
  | zero => intro v h; omega
  | succ n ih =>
    intro v h1 h2 h3
    by_cases hn : n = 0
    · subst hn
      simp at h2
      rw [D_eq 16 v (by omega)]
      simp [h2, Nat.mod_eq_of_lt h2]
    · have hge : 16 ^ n ≤ v := by
        rcases h3 with h3 | h3
        · omega
        · simpa using h3
      have h16 : 16 ≤ v := by
        have : 16 ^ 1 ≤ 16 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hv : v / 16 < 16 ^ n := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        simpa [Nat.pow_succ, Nat.mul_comm] using h2
      have hv2 : n = 1 ∨ 16 ^ (n - 1) ≤ v / 16 := by
        right
        rw [Nat.le_div_iff_mul_le (by omega)]
        have : 16 ^ (n - 1) * 16 = 16 ^ n := by
          rw [← Nat.pow_succ]; congr 1; omega
        omega
      rw [D_eq 16 v (by omega)]
      simp only [show ¬ v < 16 by omega, ite_false]
      rw [ih (v / 16) (by omega) hv hv2]
      rw [List.range_succ, List.map_append]
      congr 1
      · apply List.map_congr_left
        intro k hk
        rw [List.mem_range] at hk
        congr 2
        have : n + 1 - 1 - k = (n - 1 - k) + 1 := by omega
        rw [this, Nat.pow_succ, Nat.div_div_eq_div_mul]
        congr 1; rw [Nat.mul_comm]
      · simp

/-- `Spec.hex` is the output of `Hex()` that the implementation-shaped statement describes (`hexStrBytes v n` for the digit count `n`). -/
theorem hex_eq (v n : Nat) (h : Fv256.C.hexDigits v n) : Fv256.C.hexStrBytes v n = Fv256.Spec.hex v := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold Fv256.C.hexStrBytes Fv256.Spec.hex
  rw [toDigits_eq 16 (by omega) (by omega), D16_digits n v h1 h2 h3]
  rfl


/-- every number has a digit count `n` in the sense of `hexDigits` -/
theorem hexDigits_exists (v : Nat) : ∃ n, Fv256.C.hexDigits v n := by
  induction v using Nat.strongRecOn with
  | _ v ih =>
    by_cases h : v < 16
    · exact ⟨1, by omega, by simpa using h, Or.inl rfl⟩
    · obtain ⟨n, hn1, hn2, hn3⟩ := ih (v / 16) (Nat.div_lt_self (by omega) (by omega))
      refine ⟨n + 1, by omega, ?_, Or.inr ?_⟩
      · rw [Nat.pow_succ]
        have := (Nat.div_lt_iff_lt_mul (show 0 < 16 by omega)).1 hn2
        omega
      · show 16 ^ n ≤ v
        rcases hn3 with h3 | h3
        · subst h3; simpa using (show 16 ≤ v by omega)
        · have h4 : 16 ^ (n - 1) * 16 ≤ v := (Nat.le_div_iff_mul_le (by omega)).1 h3
          have h5 : 16 ^ n = 16 ^ (n - 1) * 16 := by
            rw [← Nat.pow_succ]; congr 1; omega
          omega

end Fv256.TextBridge
