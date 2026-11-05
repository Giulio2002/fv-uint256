import Janus
import Fv256.UtilE

open Janus Janus.Arm64 Janus.Tactic

namespace Fv256.E

/-- Sequential composition of two arm64 `ReachesRet` runs (the first ends at `t1`). -/
theorem reachesRet64_bind {p : Janus.Program} {t1 t2 : W64} {s : State}
    {Q1 Q2 : State → Prop} (h : ReachesRet p t1 s Q1)
    (h2 : ∀ s', s'.pc = t1 → Q1 s' → ReachesRet p t2 s' Q2) : ReachesRet p t2 s Q2 := by
  obtain ⟨k, s', hst, hr, hq⟩ := h
  obtain ⟨k', s'', hst', hr', hq'⟩ := h2 s' hr hq
  exact ⟨k + k', s'', hst.trans hst', hr', hq'⟩

theorem reachesRet64_mono {p : Janus.Program} {t : W64} {s : State} {Q Q' : State → Prop}
    (h : ReachesRet p t s Q) (hQ : ∀ s', Q s' → Q' s') : ReachesRet p t s Q' := by
  obtain ⟨k, s', hst, hr, hq⟩ := h
  exact ⟨k, s', hst, hr, hQ s' hq⟩

/-- A frame inside the buffer `[ptr, ptr+len)` keeps the two saved words at `sp-8` and `sp` and their accessibility. -/
theorem stack_pres64 {m m' : Janus.Arm64.Memory} {lo hi ptr len sp : Nat} (hf : MemFrame m m' [(lo, hi)])
    (h1 : ptr ≤ lo) (h2 : hi ≤ ptr + len) (hout : ptr + len ≤ sp - 8 ∨ sp + 16 ≤ ptr) (h8 : 8 ≤ sp) :
    m'.readLE (sp - 8) 8 = m.readLE (sp - 8) 8 ∧ m'.readLE sp 8 = m.readLE sp 8 ∧
      m'.accessible (sp - 8) 16 false = m.accessible (sp - 8) 16 false := by
  refine ⟨hf.readLE _ _ (by simp only [Outside, and_true]; omega), hf.readLE _ _ (by simp only [Outside, and_true]; omega),
    hf.accessible _ _ _⟩

theorem rd_mod64 (m : Janus.Arm64.Memory) (a n : Nat) (h : n ≤ 8) : m.readLE a n % 18446744073709551616 = m.readLE a n := by
  apply Nat.mod_eq_of_lt
  have := Janus.Arm64.Memory.readLE_lt m a n
  have h2 : 256 ^ n ≤ 256 ^ 8 := Nat.pow_le_pow_right (by omega) h
  have h3 : (256:Nat) ^ 8 = 18446744073709551616 := by decide
  omega

open Janus.Arm64 in
theorem copy_blk (M : Janus.Arm64.Memory) (d s n : Nat) (h1 : 16 < n) (h2 : n ≤ 32) (hdisj : d + n ≤ s ∨ s + n ≤ d) :
    ∀ i, i < n → ((((M.writeLE d 8 (M.readLE s 8)).writeLE (d + 8) 8 (M.readLE (s + 8) 8)).writeLE (n + d - 16) 8
      (M.readLE (n + s - 16) 8)).writeLE (n + d - 8) 8 (M.readLE (n + s - 8) 8)).readLE (d + i) 1 = M.readLE (s + i) 1 := by
  intro i hi
  by_cases h4 : n - 8 ≤ i
  · rw [Memory.readLE_writeLE_inside _ _ (by omega) (by omega), show d + i - (n + d - 8) = i - (n - 8) by omega,
      readLE_byte_of_window M (n + s - 8) 8 (i - (n - 8)) (by omega)]
    congr 1; omega
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    by_cases h3 : n - 16 ≤ i
    · rw [Memory.readLE_writeLE_inside _ _ (by omega) (by omega), show d + i - (n + d - 16) = i - (n - 16) by omega,
        readLE_byte_of_window M (n + s - 16) 8 (i - (n - 16)) (by omega)]
      congr 1; omega
    · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      by_cases h2' : 8 ≤ i
      · rw [Memory.readLE_writeLE_inside _ _ (by omega) (by omega), show d + i - (d + 8) = i - 8 by omega,
          readLE_byte_of_window M (s + 8) 8 (i - 8) (by omega)]
        congr 1; omega
      · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_inside _ _ (by omega) (by omega),
          show d + i - d = i by omega, readLE_byte_of_window M s 8 i (by omega)]

end Fv256.E
