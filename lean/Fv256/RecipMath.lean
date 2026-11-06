import Fv256.RecipSpec
/-!
# Pure Nat lemmas for `uint256.Reciprocal` (Newton–Raphson refinement), Extracted-free

`newtonStep A Y r` is one exact Newton step for `A / Y` from the approximation `r`: `⌊(2·r·A − r²·Y) / A⌋`.
The defect `A − r·Y` squares at every step (`newton_defect`), and the iterate never overshoots (`newton_le`).
-/

namespace Fv256.RecipMath

def newtonStep (A Y r : Nat) : Nat := (2 * r * A - r * r * Y) / A

/-- the key identity: `Y (2 r A − r² Y) + (A − r Y)² = A²` (for `r Y ≤ A`) -/
theorem newton_id (A Y r : Nat) (h : r * Y ≤ A) :
    (2 * r * A - r * r * Y) * Y + (A - r * Y) * (A - r * Y) = A * A := by
  obtain ⟨e, he⟩ : ∃ e, A = r * Y + e := ⟨A - r * Y, by omega⟩
  have hN : 2 * r * A - r * r * Y = r * (r * Y) + 2 * r * e := by
    apply Nat.sub_eq_of_eq_add
    subst he; grind
  have h3 : A - r * Y = e := by omega
  rw [hN, h3, he]
  grind

/-- Newton from below never overshoots -/
theorem newton_le (A Y r : Nat) (hA : 0 < A) (h : r * Y ≤ A) : newtonStep A Y r * Y ≤ A := by
  unfold newtonStep
  have hid := newton_id A Y r h
  have h1 : (2 * r * A - r * r * Y) / A * A ≤ 2 * r * A - r * r * Y := Nat.div_mul_le_self _ _
  have h2 : (2 * r * A - r * r * Y) / A * Y * A ≤ (2 * r * A - r * r * Y) * Y := by
    have := Nat.mul_le_mul_right Y h1
    grind
  have h3 : (2 * r * A - r * r * Y) / A * Y * A ≤ A * A := by omega
  exact Nat.le_of_mul_le_mul_right h3 hA

/-- the defect after one Newton step: `A·(A − r'·Y) ≤ (A − r·Y)² + A·Y` -/
theorem newton_defect (A Y r : Nat) (hA : 0 < A) (h : r * Y ≤ A) :
    A * (A - newtonStep A Y r * Y) ≤ (A - r * Y) * (A - r * Y) + A * Y := by
  have hid := newton_id A Y r h
  have hle := newton_le A Y r hA h
  unfold newtonStep at *
  generalize hN : 2 * r * A - r * r * Y = N at *
  have hdm := Nat.div_add_mod N A
  have hlt := Nat.mod_lt N hA
  generalize N / A = q at *
  generalize N % A = rem at *
  have h5 : q * Y * A + rem * Y = N * Y := by
    have : (A * q + rem) * Y = N * Y := by rw [hdm]
    grind
  have h6 : rem * Y ≤ A * Y := Nat.mul_le_mul_right _ (Nat.le_of_lt hlt)
  have h7 : A * (A - q * Y) + q * Y * A = A * A := by
    have := Nat.sub_add_cancel hle
    have : A * (A - q * Y) + A * (q * Y) = A * A := by rw [← Nat.mul_add, this]
    grind
  omega

/-! ## Signed Newton steps with a perturbation window (Int) -/

theorem sq_le (a b : Int) (h : -b ≤ a ∧ a ≤ b) : a * a ≤ b * b := by
  have hb : 0 ≤ b := by omega
  rcases Int.le_total 0 a with h0 | h0
  · exact Int.mul_le_mul h.2 h.2 h0 hb
  · have : (-a) * (-a) ≤ b * b := Int.mul_le_mul (by omega) (by omega) (by omega) hb
    rw [Int.neg_mul_neg] at this
    exact this

/-- the exact identity behind every Newton step: for `r' = 2r - T`, `A (A - r' Y) = (A - r Y)² + Y (A T - r² Y)` -/
theorem step_id (A Y r T r' : Int) (h : r' = 2 * r - T) :
    A * (A - r' * Y) = (A - r * Y) * (A - r * Y) + Y * (A * T - r * r * Y) := by
  subst h; grind

/-- a Newton step whose subtracted term `T` is within `c` (relatively to `A`) of `r² Y / A`:
`|A - r Y| ≤ B` gives `|A - r' Y| ≤ B'` as soon as `A B' ≥ B² + c A Y` -/
theorem mul_self_nonneg' (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (a := -a) (b := -a) (by omega) (by omega)
    rw [Int.neg_mul_neg] at this
    exact this

theorem step_bound (A Y r T r' B B' c : Int) (hA : 0 < A) (hY : 0 < Y) (hc : 0 ≤ c) (h : r' = 2 * r - T)
    (hT : -(c * A) ≤ A * T - r * r * Y ∧ A * T - r * r * Y ≤ c * A)
    (hd : -B ≤ A - r * Y ∧ A - r * Y ≤ B) (hB : B * B + c * A * Y ≤ A * B') (hB2 : c * Y ≤ B') :
    -B' ≤ A - r' * Y ∧ A - r' * Y ≤ B' := by
  have hid := step_id A Y r T r' h
  have hsq := sq_le _ _ hd
  have hsq0 := mul_self_nonneg' (A - r * Y)
  have hY1 : Y * (A * T - r * r * Y) ≤ Y * (c * A) := Int.mul_le_mul_of_nonneg_left hT.2 (Int.le_of_lt hY)
  have hY2 : Y * (-(c * A)) ≤ Y * (A * T - r * r * Y) := Int.mul_le_mul_of_nonneg_left hT.1 (Int.le_of_lt hY)
  have e1 : Y * (-(c * A)) = -(c * A * Y) := by grind
  have e2 : Y * (c * A) = c * A * Y := by grind
  have e3 : c * A * Y ≤ A * B' := by
    have : c * Y * A ≤ B' * A := Int.mul_le_mul_of_nonneg_right hB2 (Int.le_of_lt hA)
    grind
  rw [e1] at hY2
  rw [e2] at hY1
  have hcomm : (A - r' * Y) * A = A * (A - r' * Y) := Int.mul_comm _ _
  have k1 : -B' * A = -(A * B') := by grind
  have k2 : B' * A = A * B' := Int.mul_comm _ _
  generalize (A - r * Y) * (A - r * Y) = P at *
  generalize Y * (A * T - r * r * Y) = Q at *
  generalize A * (A - r' * Y) = R at *
  generalize c * A * Y = S at *
  have hR1 : -(A * B') ≤ R := by omega
  have hR2 : R ≤ A * B' := by omega
  constructor
  · have : -B' * A ≤ (A - r' * Y) * A := by rw [k1, hcomm]; exact hR1
    exact Int.le_of_mul_le_mul_right this hA
  · have : (A - r' * Y) * A ≤ B' * A := by rw [k2, hcomm]; exact hR2
    exact Int.le_of_mul_le_mul_right this hA

/-! ## The four stages -/

/-- stages 0 -> 1, 1 -> 2, 2 -> 3: the defect bounds -/
theorem stage1 (y R0 r1 T : Int) (hy : 2 ^ 255 ≤ y ∧ y < 2 ^ 256) (h : r1 = 2 * R0 - T)
    (hT : -(8 * 2 ^ 319) ≤ 2 ^ 319 * T - R0 * R0 * y ∧ 2 ^ 319 * T - R0 * R0 * y ≤ 8 * 2 ^ 319)
    (hd : -(2 ^ 288) ≤ 2 ^ 319 - R0 * y ∧ 2 ^ 319 - R0 * y ≤ 2 ^ 288) :
    -(2 ^ 260) ≤ 2 ^ 319 - r1 * y ∧ 2 ^ 319 - r1 * y ≤ 2 ^ 260 :=
  step_bound (2 ^ 319) y R0 T r1 (2 ^ 288) (2 ^ 260) 8 (by omega) (by omega) (by omega) h hT hd
    (by omega) (by omega)

theorem stage2 (y R1 r2 T : Int) (hy : 2 ^ 255 ≤ y ∧ y < 2 ^ 256) (h : r2 = 2 * R1 - T)
    (hT : -(8 * 2 ^ 383) ≤ 2 ^ 383 * T - R1 * R1 * y ∧ 2 ^ 383 * T - R1 * R1 * y ≤ 8 * 2 ^ 383)
    (hd : -(2 ^ 324) ≤ 2 ^ 383 - R1 * y ∧ 2 ^ 383 - R1 * y ≤ 2 ^ 324) :
    -(2 ^ 266) ≤ 2 ^ 383 - r2 * y ∧ 2 ^ 383 - r2 * y ≤ 2 ^ 266 :=
  step_bound (2 ^ 383) y R1 T r2 (2 ^ 324) (2 ^ 266) 8 (by omega) (by omega) (by omega) h hT hd
    (by omega) (by omega)

theorem stage3 (y R2 r3 T : Int) (hy : 2 ^ 255 ≤ y ∧ y < 2 ^ 256) (h : r3 = 2 * R2 - T)
    (hT : -(8 * 2 ^ 447) ≤ 2 ^ 447 * T - R2 * R2 * y ∧ 2 ^ 447 * T - R2 * R2 * y ≤ 8 * 2 ^ 447)
    (hd : -(2 ^ 330) ≤ 2 ^ 447 - R2 * y ∧ 2 ^ 447 - R2 * y ≤ 2 ^ 330) :
    -(2 ^ 260) ≤ 2 ^ 447 - r3 * y ∧ 2 ^ 447 - r3 * y ≤ 2 ^ 260 :=
  step_bound (2 ^ 447) y R2 T r3 (2 ^ 330) (2 ^ 260) 8 (by omega) (by omega) (by omega) h hT hd
    (by omega) (by omega)

/-- the last stage: `r4 = u 2^128 - K` with `K = ⌈x / 2^128⌉`, `x 2^192 = u² y - D` (`0 ≤ D < 2^258`) -/
theorem stage4 (y u D K : Int) (hy : 2 ^ 255 ≤ y ∧ y < 2 ^ 256)
    (hd : -(2 ^ 260) ≤ 2 ^ 447 - u * y ∧ 2 ^ 447 - u * y ≤ 2 ^ 260) (hD : 0 ≤ D ∧ D < 2 ^ 258)
    (hK : u * u * y - D ≤ 2 ^ 320 * K ∧ 2 ^ 320 * K < u * u * y - D + 2 ^ 320) :
    2 ^ 574 - y - 2 ^ 200 ≤ (u * 2 ^ 128 - K) * y ∧ (u * 2 ^ 128 - K) * y ≤ 2 ^ 574 + 2 ^ 200 := by
  have hsq := sq_le _ _ hd
  have hsq0 := mul_self_nonneg' (2 ^ 447 - u * y)
  have key : 2 ^ 320 * (2 ^ 574 - (u * 2 ^ 128 - K) * y) =
      (2 ^ 447 - u * y) * (2 ^ 447 - u * y) + y * (2 ^ 320 * K - u * u * y) := by grind
  have hy0 : 0 < y := by omega
  have h1 : y * (-D) ≤ y * (2 ^ 320 * K - u * u * y) :=
    Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt hy0)
  have h2 : y * (2 ^ 320 * K - u * u * y) ≤ y * (2 ^ 320) :=
    Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt hy0)
  have h3 : y * D ≤ y * 2 ^ 258 := Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt hy0)
  have h4 : y * (-D) = -(y * D) := by grind
  generalize y * (2 ^ 320 * K - u * u * y) = Q at *
  generalize (2 ^ 447 - u * y) * (2 ^ 447 - u * y) = P at *
  generalize y * D = YD at *
  generalize (u * 2 ^ 128 - K) * y = V at *
  constructor <;> omega

/-- the final decrement: `r4' = if A < r4 y then r4 - 1 else r4` lies in `[E - 1, E]`, `E = A / y`
(`A ≤ r4 y + y + δ`, `r4 y ≤ A + δ`, `δ < y`) -/
theorem adjust (A y r4 δ : Nat) (hδ : δ < y) (hlo : A ≤ r4 * y + y + δ) (hhi : r4 * y ≤ A + δ) :
    A / y - 1 ≤ (if A < r4 * y then r4 - 1 else r4) ∧ (if A < r4 * y then r4 - 1 else r4) ≤ A / y := by
  have hy0 : 0 < y := by omega
  have hdm := Nat.div_add_mod A y
  have hlt := Nat.mod_lt A hy0
  generalize A / y = E at *
  generalize A % y = rem at *
  have c1 : y * E = E * y := Nat.mul_comm _ _
  have h1 : r4 < E + 2 := by
    rcases Nat.lt_or_ge r4 (E + 2) with h | hn
    · exact h
    · exfalso
      have := Nat.mul_le_mul_right y hn
      have e : (E + 2) * y = E * y + 2 * y := by grind
      omega
  have h2 : E ≤ r4 + 1 := by
    rcases Nat.lt_or_ge (r4 + 1) E with hn | h
    · exfalso
      have := Nat.mul_le_mul_right y (show r4 + 2 ≤ E by omega)
      have e : (r4 + 2) * y = r4 * y + 2 * y := by grind
      omega
    · omega
  split
  · rename_i hc
    have h3 : E < r4 := by
      rcases Nat.lt_or_ge E r4 with h | hn
      · exact h
      · exfalso
        have := Nat.mul_le_mul_right y hn
        omega
    omega
  · rename_i hc
    have h3 : r4 ≤ E := by
      rcases Nat.lt_or_ge E r4 with hn | h
      · exfalso
        have := Nat.mul_le_mul_right y (show E + 1 ≤ r4 by omega)
        have e : (E + 1) * y = E * y + y := by grind
        omega
      · exact h
    omega


/-! ## From `r4'` to the `Reciprocal` windows -/

theorem pow2_dvd (n : Nat) : ∀ m, m ∣ 2 ^ n → ∃ i, m = 2 ^ i := by
  induction n with
  | zero => intro m h; exact ⟨0, by simpa using Nat.dvd_one.1 h⟩
  | succ n ih =>
    intro m h
    obtain ⟨k, hk⟩ : ∃ k, m = 2 * k ∨ m = 2 * k + 1 := ⟨m / 2, by omega⟩
    rcases hk with hk | hk
    · subst hk
      have h' : 2 * k ∣ 2 * 2 ^ n := by rw [← Nat.pow_succ']; exact h
      have := ih k (Nat.dvd_of_mul_dvd_mul_left (by omega) h')
      obtain ⟨i, hi⟩ := this
      exact ⟨i + 1, by rw [Nat.pow_succ']; omega⟩
    · subst hk
      have hc : Nat.Coprime (2 * k + 1) 2 := by
        unfold Nat.Coprime
        rw [Nat.gcd_comm, Nat.gcd_rec]
        have : (2 * k + 1) % 2 = 1 := by omega
        rw [this]; rfl
      have h' : 2 * k + 1 ∣ 2 * 2 ^ n := by rw [← Nat.pow_succ']; exact h
      exact ih _ (hc.dvd_of_dvd_mul_left h')

theorem pred_div (N m : Nat) (hm : 0 < m) (hnd : ¬ m ∣ N) : (N - 1) / m = N / m := by
  have hdm := Nat.div_add_mod N m
  have hlt := Nat.mod_lt N hm
  have hr : N % m ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
  generalize N / m = q at *
  generalize N % m = r at *
  have : (m * q + r - 1) / m = q := by
    apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_comm]; omega
    · rw [Nat.add_mul, Nat.mul_comm]; omega
  rw [← hdm]
  exact this

theorem shiftdiv (a b m : Nat) : 2 ^ (a + b) / (m * 2 ^ b) = 2 ^ a / m := by
  rw [Nat.pow_add, Nat.mul_comm m (2 ^ b), Nat.mul_comm (2 ^ a) (2 ^ b)]
  exact Nat.mul_div_mul_left _ _ (Nat.two_pow_pos b)

theorem ex_eq (m : Nat) (hm : 0 < m) (hnp : ∀ i, m ≠ 2 ^ i) : (2 ^ 512 - 1) / m = 2 ^ 512 / m :=
  pred_div _ m hm (fun h => by
    obtain ⟨i, hi⟩ := pow2_dvd 512 m h
    exact hnp i hi)

theorem div_pred (E d : Nat) (hd : 0 < d) : E / d ≤ (E - 1) / d + 1 := by
  have hdm := Nat.div_add_mod (E - 1) d
  have hlt := Nat.mod_lt (E - 1) hd
  generalize (E - 1) / d = t at *
  generalize (E - 1) % d = rr at *
  apply Nat.div_le_of_le_mul
  rw [Nat.mul_add, Nat.mul_one]
  omega

theorem double_div (N m : Nat) (hm : 0 < m) : 2 * (N / m) ≤ 2 * N / m ∧ 2 * N / m ≤ 2 * (N / m) + 1 := by
  have hdm := Nat.div_add_mod N m
  have hlt := Nat.mod_lt N hm
  generalize N / m = q at *
  generalize N % m = r at *
  subst hdm
  constructor
  · apply (Nat.le_div_iff_mul_le hm).2
    have : 2 * q * m = 2 * (m * q) := by rw [Nat.mul_assoc, Nat.mul_comm q m]
    omega
  · apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hm).2
    have : (2 * q + 1).succ * m = 2 * (m * q) + 2 * m := by
      rw [Nat.succ_eq_add_one, Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_comm q m]; omega
    omega

/-- `r4' ∈ [E-1, E]` to the `Reciprocal` windows -/
theorem mu_window (m s r4 mu : Nat) (hs : s ≤ 63) (hm : 2 ^ (255 - s) ≤ m ∧ m < 2 ^ (256 - s))
    (hnp : ∀ i, m ≠ 2 ^ i) (hr : 2 ^ 574 / (m * 2 ^ s) - 1 ≤ r4 ∧ r4 ≤ 2 ^ 574 / (m * 2 ^ s))
    (hmu1 : s ≤ 62 → mu = r4 / 2 ^ (62 - s)) (hmu2 : s = 63 → mu = 2 * r4) :
    Fv256.F.RecipWeak m mu ∧ (s ≤ 62 → Fv256.F.RecipOK m mu) := by
  have hm0 : 0 < m := by
    have : 0 < 2 ^ (255 - s) := Nat.two_pow_pos _
    omega
  have hex := ex_eq m hm0 hnp
  unfold Fv256.F.RecipWeak Fv256.F.RecipOK Fv256.F.recipExact
  rw [hex]
  by_cases h63 : s = 63
  · subst h63
    have hmu := hmu2 rfl
    have e1 : 2 ^ 574 / (m * 2 ^ 63) = 2 ^ 511 / m := shiftdiv 511 63 m
    rw [e1] at hr
    have e2 : 2 ^ 512 = 2 * 2 ^ 511 := by rw [← Nat.pow_succ']
    have hdd := double_div (2 ^ 511) m hm0
    rw [← e2] at hdd
    generalize 2 ^ 511 / m = E at hr hdd
    have hq1 : 2 * E ≤ 2 ^ 512 / m := by
      generalize 2 ^ 512 / m = q at *; omega
    have hq2 : 2 ^ 512 / m ≤ 2 * E + 1 := by
      generalize 2 ^ 512 / m = q at *; omega
    refine ⟨⟨by omega, by omega⟩, fun h => by omega⟩
  · have hs62 : s ≤ 62 := by omega
    have hmu := hmu1 hs62
    have e1 : 2 ^ 574 / (m * 2 ^ s) / 2 ^ (62 - s) = 2 ^ 512 / m := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_assoc, ← Nat.pow_add,
        show s + (62 - s) = 62 by omega]
      exact shiftdiv 512 62 m
    generalize 2 ^ 574 / (m * 2 ^ s) = E at hr e1
    have hd := Nat.two_pow_pos (62 - s)
    generalize 2 ^ (62 - s) = d at *
    generalize 2 ^ 512 / m = q at *
    have hle : mu ≤ q := by
      rw [hmu, ← e1]; exact Nat.div_le_div_right hr.2
    have hge : q ≤ mu + 1 := by
      rw [hmu, ← e1]
      have h1 : (E - 1) / d ≤ r4 / d := Nat.div_le_div_right hr.1
      have h2 : E / d ≤ (E - 1) / d + 1 := by
        exact div_pred E d hd
      omega
    exact ⟨⟨by omega, hle⟩, fun _ => ⟨by omega, hle⟩⟩

end Fv256.RecipMath
