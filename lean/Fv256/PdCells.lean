import Janus
import Fv256.SpecE
import Fv256.PrettyMath

/-!
# The `out` array of `PrettyDec` as a stream of cells (ISA-independent)

`PrettyDec` fills a 133-byte array `out` from the right.  Cell `p` is the byte `p` places from the end (address `top - p`).
After the first `c` cells have been produced, the array holds `pcell sep z p` in cell `p < c` and the initial `'0'` elsewhere
(`OutIs`).  `cOf D` is the number of cells produced once `D` digits are placed: the separator before a digit is written lazily,
so no trailing separator is ever produced (`cOf 3 = 3`, `cOf 4 = 5`).
-/

namespace Fv256.E

open Janus.Arm64

/-- cell `p` when the first `c` cells have been produced -/
def pout (sep z c p : Nat) : Nat := if p < c then pcell sep z p else 48

/-- the array `out`: cell `p` at address `top - p` (`p < 133`) -/
def OutIs (M : Memory) (top sep z c : Nat) : Prop := ∀ p, p < 133 → M.readLE (top - p) 1 = pout sep z c p

/-- cells produced once `D` digits are placed -/
def cOf (D : Nat) : Nat := if D = 0 then 0 else D + (D - 1) / 3

theorem OutIs.zero {M : Memory} {top : Nat} (sep z : Nat) (h : ∀ p, p < 133 → M.readLE (top - p) 1 = 48) :
    OutIs M top sep z 0 := by
  intro p hp; rw [h p hp]; simp [pout]

theorem OutIs.pad {M : Memory} {top sep z c : Nat} (h : OutIs M top sep z c) (hp : pcell sep z c = 48) :
    OutIs M top sep z (c + 1) := by
  intro p hpl
  rw [h p hpl]
  unfold pout
  by_cases h1 : p < c
  · simp [h1, show p < c + 1 by omega]
  · by_cases h2 : p = c
    · subst h2; simp [hp]
    · simp [h1, show ¬ p < c + 1 by omega]

theorem OutIs.write {M : Memory} {top sep z c : Nat} (h : OutIs M top sep z c) (htop : 132 ≤ top) (hc : c < 133) (v : Nat)
    (hv : v % 256 = pcell sep z c) : OutIs (M.writeLE (top - c) 1 v) top sep z (c + 1) := by
  intro p hpl
  by_cases h2 : p = c
  · subst h2
    rw [Memory.readLE_writeLE_self]
    simp [pout, hv]
  · rw [Memory.readLE_writeLE_of_disjoint (m := M) (a := top - c) (n := 1) (b := top - p) (k := 1) v (by omega), h p hpl]
    unfold pout
    by_cases h1 : p < c
    · simp [h1, show p < c + 1 by omega]
    · simp [h1, show ¬ p < c + 1 by omega]

theorem OutIs.of_agree {M M' : Memory} {top sep z c : Nat} (h : OutIs M top sep z c) (htop : 132 ≤ top)
    (hag : ∀ p, p < 133 → M'.readLE (top - p) 1 = M.readLE (top - p) 1) : OutIs M' top sep z c := by
  intro p hp; rw [hag p hp]; exact h p hp

/-- cells of `D` digits followed by one more digit: the next cell index -/
def nd (c : Nat) : Nat := if c % 4 = 3 then c + 2 else c + 1

theorem cOf_zero : cOf 0 = 0 := by simp [cOf]

theorem cOf_succ (D : Nat) : cOf (D + 1) = nd (cOf D) := by
  unfold cOf nd
  by_cases h : D = 0
  · subst h; simp
  · simp only [h, if_false, show D + 1 ≠ 0 by omega]
    split <;> omega

theorem cOf_mod (D : Nat) (h : 1 ≤ D) : cOf D % 4 ≠ 0 := by
  unfold cOf; simp only [show D ≠ 0 by omega, if_false]; omega

theorem cOf_dgt (D : Nat) : cOf D - cOf D / 4 = D := by
  unfold cOf; split <;> omega

/-- the digit cell: the cell written by the next digit when `c` cells are done, and its digit index -/
theorem nd_digit (c : Nat) : (nd c - 1) % 4 ≠ 3 ∧ (nd c - 1) - (nd c - 1) / 4 = c - c / 4 := by
  unfold nd; split <;> omega

theorem pcell_digit (sep z p : Nat) (h : p % 4 ≠ 3) : pcell sep z p = 48 + z / 10 ^ (p - p / 4) % 10 := by
  unfold pcell; rw [if_neg h]

theorem pcell_sep (sep z p : Nat) (h : p % 4 = 3) : pcell sep z p = sep := by
  unfold pcell; rw [if_pos h]

/-- The digit cell written for digit `D` (cell `cOf (D+1) - 1`) holds `48 + z / 10^D % 10`. -/
theorem pcell_cOf (sep z D : Nat) : pcell sep z (cOf (D + 1) - 1) = 48 + z / 10 ^ D % 10 := by
  have hc := cOf_dgt (D + 1)
  have h4 := cOf_mod (D + 1) (by omega)
  have : cOf (D + 1) - 1 - (cOf (D + 1) - 1) / 4 = D := by omega
  rw [pcell_digit sep z _ (by omega), this]

/-- the total number of cells of `decLen z` digits -/
theorem cOf_plen (z : Nat) : cOf (decLen z) = plen z := by
  have := decLen_pos z
  unfold cOf plen; simp only [show decLen z ≠ 0 by omega, if_false]

end Fv256.E

namespace Fv256.E

theorem cOf_mono (a b : Nat) (h : a ≤ b) : cOf a ≤ cOf b := by
  unfold cOf
  split <;> split <;> omega

end Fv256.E
