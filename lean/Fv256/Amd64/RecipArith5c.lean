import Janus
set_option maxRecDepth 100000
theorem hdl3 (a : Nat) : (decide (0 < a)).toNat = if a = 0 then 0 else 1 := by
  by_cases h : a = 0
  · subst h; decide
  · have : 0 < a := Nat.pos_of_ne_zero h
    simp [h, this]
theorem sum5c (m100 rsi r12 r10 r8 r15 rax rdx r13 xb9frdx : Nat)
  (b0 : m100 < 2^64) (b1 : rsi < 2^64) (b2 : r12 < 2^64) (b3 : r10 < 2^64) (b4 : r8 < 2^64) (b5 : r15 < 2^64) (b6 : rax < 2^64) (b7 : rdx < 2^64) (b8 : r13 < 2^64)
  (h : xb9frdx = (if 4611686018427387904 < r13 + (decide (0 < rdx + (decide (0 < rax + (decide (0 < r15 + (decide (0 < r8 + (decide (0 < r10 + (decide (0 < r12 + (decide (0 < rsi + (decide (0 < m100)).toNat)).toNat)).toNat)).toNat)).toNat)).toNat)).toNat)).toNat then 1 else 0)) :
  xb9frdx = if 2^574 < m100 + 2^64 * rsi + 2^128 * r12 + 2^192 * r10 + 2^256 * r8 + 2^320 * r15 + 2^384 * rax + 2^448 * rdx + 2^512 * r13 then 1 else 0 := by
  simp only [hdl3] at h
  generalize hz0 : (if m100 = 0 then 0 else 1) = z0 at h
  generalize hz1 : (if rsi + z0 = 0 then 0 else 1) = z1 at h
  generalize hz2 : (if r12 + z1 = 0 then 0 else 1) = z2 at h
  generalize hz3 : (if r10 + z2 = 0 then 0 else 1) = z3 at h
  generalize hz4 : (if r8 + z3 = 0 then 0 else 1) = z4 at h
  generalize hz5 : (if r15 + z4 = 0 then 0 else 1) = z5 at h
  generalize hz6 : (if rax + z5 = 0 then 0 else 1) = z6 at h
  generalize hz7 : (if rdx + z6 = 0 then 0 else 1) = z7 at h
  have f0 : z0 ≤ 1 ∧ (z0 = 0 ↔ m100 = 0) := by revert hz0; split <;> omega
  have f1 : z1 ≤ 1 ∧ (z1 = 0 ↔ rsi = 0 ∧ z0 = 0) := by revert hz1; split <;> omega
  have f2 : z2 ≤ 1 ∧ (z2 = 0 ↔ r12 = 0 ∧ z1 = 0) := by revert hz2; split <;> omega
  have f3 : z3 ≤ 1 ∧ (z3 = 0 ↔ r10 = 0 ∧ z2 = 0) := by revert hz3; split <;> omega
  have f4 : z4 ≤ 1 ∧ (z4 = 0 ↔ r8 = 0 ∧ z3 = 0) := by revert hz4; split <;> omega
  have f5 : z5 ≤ 1 ∧ (z5 = 0 ↔ r15 = 0 ∧ z4 = 0) := by revert hz5; split <;> omega
  have f6 : z6 ≤ 1 ∧ (z6 = 0 ↔ rax = 0 ∧ z5 = 0) := by revert hz6; split <;> omega
  have f7 : z7 ≤ 1 ∧ (z7 = 0 ↔ rdx = 0 ∧ z6 = 0) := by revert hz7; split <;> omega
  rw [h]
  split <;> split <;> omega
