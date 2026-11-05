import Fv256.SpecE

/-!
# Specification of `PrettyDec` (family E)

`PrettyDec(sep)` writes the decimal digits of `z` with the byte `sep` between every group of three digits, counted from the
right (thousands separators): `1234567` becomes `1,234,567` for `sep = ','`, and numbers below `1000` have none.
-/

namespace Fv256.E

/-- The three digits of `n % 1000`, zero padded. -/
def pad3 (n : Nat) : List Nat := [48 + n / 100 % 10, 48 + n / 10 % 10, 48 + n % 10]

/-- The decimal digits of `n` with `sep` between every group of three digits, counted from the right:
a number below `1000` is its digits; otherwise the grouped digits of `n / 1000`, then `sep`, then the three digits of `n % 1000`. -/
def prettyBytes (sep : Nat) (n : Nat) : List Nat :=
  if h : n < 1000 then decBytes n else prettyBytes sep (n / 1000) ++ sep :: pad3 (n % 1000)
termination_by n
decreasing_by omega

theorem prettyBytes_lt (sep n : Nat) (h : n < 1000) : prettyBytes sep n = decBytes n := by
  rw [prettyBytes]; simp [h]

theorem prettyBytes_ge (sep n : Nat) (h : 1000 ≤ n) :
    prettyBytes sep n = prettyBytes sep (n / 1000) ++ sep :: pad3 (n % 1000) := by
  rw [prettyBytes]; simp [Nat.not_lt.mpr h]

/-- The stream of output cells read from the right: position `p` (`0` the last byte) holds the separator when `p % 4 = 3`
and otherwise the digit number `p - p / 4` from the right. -/
def pcell (sep v p : Nat) : Nat := if p % 4 = 3 then sep else 48 + v / 10 ^ (p - p / 4) % 10

/-- The number of output bytes. -/
def plen (v : Nat) : Nat := decLen v + (decLen v - 1) / 3

theorem prettyBytes_length (sep n : Nat) : (prettyBytes sep n).length = plen n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 1000
    · rw [prettyBytes_lt sep n h]
      have : decLen n ≤ 3 := decLen_le_of_lt_pow n 3 (by omega) (by show n < 1000; omega)
      simp only [plen]; show decLen n = _
      omega
    · rw [prettyBytes_ge sep n (by omega)]
      simp only [List.length_append, List.length_cons, pad3, List.length_nil]
      rw [ih (n / 1000) (by omega)]
      have : decLen n = decLen (n / 1000) + 3 := by
        have := decLen_div_pow n 3 (by show 1000 ≤ n; omega)
        simpa using this
      have hp := decLen_pos (n / 1000)
      simp only [plen]
      omega

theorem pcell_add4 (sep v p : Nat) : pcell sep v (p + 4) = pcell sep (v / 1000) p := by
  unfold pcell
  have h1 : (p + 4) % 4 = p % 4 := by omega
  have h2 : p + 4 - (p + 4) / 4 = (p - p / 4) + 3 := by omega
  rw [h1, h2]
  split
  · rfl
  · rw [Nat.pow_add, Nat.div_div_eq_div_mul]
    simp only [Nat.reducePow]
    rw [Nat.mul_comm]

theorem getD_append_right' (a b : List Nat) (j : Nat) (h : a.length ≤ j) : (a ++ b).getD j 0 = b.getD (j - a.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- The bytes of `prettyBytes`, read from the left, are the cells read from the right. -/
theorem prettyBytes_getD (sep n : Nat) :
    ∀ j, j < plen n → (prettyBytes sep n).getD j 0 = pcell sep n (plen n - 1 - j) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro j hj
    by_cases h : n < 1000
    · rw [prettyBytes_lt sep n h]
      have hl : decLen n ≤ 3 := decLen_le_of_lt_pow n 3 (by omega) (by show n < 1000; omega)
      have hp : plen n = decLen n := by simp only [plen]; omega
      rw [hp] at hj ⊢
      have e := decBytes_getD_rev n (decLen n - 1 - j) (by omega)
      rw [show decLen n - 1 - (decLen n - 1 - j) = j by omega] at e
      rw [e]
      unfold pcell
      have h3 : (decLen n - 1 - j) % 4 ≠ 3 := by omega
      rw [if_neg h3, show decLen n - 1 - j - (decLen n - 1 - j) / 4 = decLen n - 1 - j by omega]
    · have hn1 : 1000 ≤ n := by omega
      rw [prettyBytes_ge sep n hn1]
      have hlen := prettyBytes_length sep (n / 1000)
      have hd : decLen n = decLen (n / 1000) + 3 := by
        have := decLen_div_pow n 3 (by show 1000 ≤ n; omega)
        simpa using this
      have hp1 := decLen_pos (n / 1000)
      have hpl : plen n = plen (n / 1000) + 4 := by simp only [plen]; omega
      rw [hpl] at hj ⊢
      by_cases hj1 : j < plen (n / 1000)
      · rw [Fv256.E.getD_append_left _ _ _ (by omega)]
        rw [show plen (n / 1000) + 4 - 1 - j = (plen (n / 1000) - 1 - j) + 4 by omega, pcell_add4]
        have := ih (n / 1000) (by omega) j hj1
        exact this
      · have hr : j - (prettyBytes sep (n / 1000)).length = j - plen (n / 1000) := by rw [hlen]
        rw [getD_append_right' _ _ _ (by omega), hr]
        have hjj : j - plen (n / 1000) < 4 := by omega
        rcases (by omega : j - plen (n / 1000) = 0 ∨ j - plen (n / 1000) = 1 ∨ j - plen (n / 1000) = 2 ∨ j - plen (n / 1000) = 3) with h0 | h0 | h0 | h0
        · have hix : plen (n / 1000) + 4 - 1 - j = 3 := by omega
          rw [h0, hix]; simp [pcell]
        · have hix : plen (n / 1000) + 4 - 1 - j = 2 := by omega
          rw [h0, hix]; simp [pad3, pcell]; try omega
        · have hix : plen (n / 1000) + 4 - 1 - j = 1 := by omega
          rw [h0, hix]; simp [pad3, pcell]; try omega
        · have hix : plen (n / 1000) + 4 - 1 - j = 0 := by omega
          rw [h0, hix]; simp [pad3, pcell]; try omega

