import Janus

/-! Shared lemmas: the 256-bit value at a pointer as four 64-bit limbs, and bitwise operations limb by limb. -/

namespace Fv256.Util

theorem readLE_32 (m : Janus.Arm64.Memory) (a : Nat) :
    m.readLE a 32 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 +
      2 ^ 128 * m.readLE (a + 16) 8 + 2 ^ 192 * m.readLE (a + 24) 8 := by
  rw [show 32 = 8 + 24 from rfl, Janus.Arm64.Memory.readLE_add, show 24 = 8 + 16 from rfl,
    Janus.Arm64.Memory.readLE_add, show 16 = 8 + 8 from rfl, Janus.Arm64.Memory.readLE_add]
  simp only [Nat.add_assoc]
  omega

/-- bitwise ops split at a bit boundary -/
theorem and_split (k a b c d : Nat) (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    (a + 2 ^ k * c) &&& (b + 2 ^ k * d) = (a &&& b) + 2 ^ k * (c &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hab : a &&& b < 2 ^ k := Nat.and_lt_two_pow _ hb
  rw [Nat.testBit_and, Nat.add_comm a, Nat.add_comm b, Nat.add_comm (a &&& b),
    Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hab]
  by_cases h : i < k
  · simp [h, Nat.testBit_and]
  · simp [h, Nat.testBit_and]

theorem or_split (k a b c d : Nat) (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    (a + 2 ^ k * c) ||| (b + 2 ^ k * d) = (a ||| b) + 2 ^ k * (c ||| d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hab : a ||| b < 2 ^ k := Nat.or_lt_two_pow ha hb
  rw [Nat.testBit_or, Nat.add_comm a, Nat.add_comm b, Nat.add_comm (a ||| b),
    Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hab]
  by_cases h : i < k
  · simp [h, Nat.testBit_or]
  · simp [h, Nat.testBit_or]

theorem xor_split (k a b c d : Nat) (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    (a + 2 ^ k * c) ^^^ (b + 2 ^ k * d) = (a ^^^ b) + 2 ^ k * (c ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hab : a ^^^ b < 2 ^ k := Nat.xor_lt_two_pow ha hb
  rw [Nat.testBit_xor, Nat.add_comm a, Nat.add_comm b, Nat.add_comm (a ^^^ b),
    Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hab]
  by_cases h : i < k
  · simp [h, Nat.testBit_xor]
  · simp [h, Nat.testBit_xor]


theorem readLE8_lt (m : Janus.Arm64.Memory) (a : Nat) : m.readLE a 8 < 18446744073709551616 := by
  simpa using Janus.Arm64.Memory.readLE_lt m a 8

theorem and4 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (g0 : b0 < 18446744073709551616) (g1 : b1 < 18446744073709551616)
    (g2 : b2 < 18446744073709551616) :
    (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3) &&&
      (b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3) =
    (a0 &&& b0) + 18446744073709551616 * (a1 &&& b1) + 340282366920938463463374607431768211456 * (a2 &&& b2) +
        6277101735386680763835789423207666416102355444464034512896 * (a3 &&& b3) := by
  have h := and_split 64 a0 b0 (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3)) (b1 + 2 ^ 64 * (b2 + 2 ^ 64 * b3)) (by simpa using h0) (by simpa using g0)
  have h' := and_split 64 a1 b1 (a2 + 2 ^ 64 * a3) (b2 + 2 ^ 64 * b3) (by simpa using h1) (by simpa using g1)
  have h'' := and_split 64 a2 b2 a3 b3 (by simpa using h2) (by simpa using g2)
  have e : (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3) =
      a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3)) := by omega
  have e' : (b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3) =
      b0 + 2 ^ 64 * (b1 + 2 ^ 64 * (b2 + 2 ^ 64 * b3)) := by omega
  rw [e, e', h, h', h'']
  omega

theorem or4 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (g0 : b0 < 18446744073709551616) (g1 : b1 < 18446744073709551616)
    (g2 : b2 < 18446744073709551616) :
    (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3) |||
      (b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3) =
    (a0 ||| b0) + 18446744073709551616 * (a1 ||| b1) + 340282366920938463463374607431768211456 * (a2 ||| b2) +
        6277101735386680763835789423207666416102355444464034512896 * (a3 ||| b3) := by
  have h := or_split 64 a0 b0 (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3)) (b1 + 2 ^ 64 * (b2 + 2 ^ 64 * b3)) (by simpa using h0) (by simpa using g0)
  have h' := or_split 64 a1 b1 (a2 + 2 ^ 64 * a3) (b2 + 2 ^ 64 * b3) (by simpa using h1) (by simpa using g1)
  have h'' := or_split 64 a2 b2 a3 b3 (by simpa using h2) (by simpa using g2)
  have e : (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3) =
      a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3)) := by omega
  have e' : (b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3) =
      b0 + 2 ^ 64 * (b1 + 2 ^ 64 * (b2 + 2 ^ 64 * b3)) := by omega
  rw [e, e', h, h', h'']
  omega

theorem xor4 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (g0 : b0 < 18446744073709551616) (g1 : b1 < 18446744073709551616)
    (g2 : b2 < 18446744073709551616) :
    (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3) ^^^
      (b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3) =
    (a0 ^^^ b0) + 18446744073709551616 * (a1 ^^^ b1) + 340282366920938463463374607431768211456 * (a2 ^^^ b2) +
        6277101735386680763835789423207666416102355444464034512896 * (a3 ^^^ b3) := by
  have h := xor_split 64 a0 b0 (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3)) (b1 + 2 ^ 64 * (b2 + 2 ^ 64 * b3)) (by simpa using h0) (by simpa using g0)
  have h' := xor_split 64 a1 b1 (a2 + 2 ^ 64 * a3) (b2 + 2 ^ 64 * b3) (by simpa using h1) (by simpa using g1)
  have h'' := xor_split 64 a2 b2 a3 b3 (by simpa using h2) (by simpa using g2)
  have e : (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3) =
      a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3)) := by omega
  have e' : (b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3) =
      b0 + 2 ^ 64 * (b1 + 2 ^ 64 * (b2 + 2 ^ 64 * b3)) := by omega
  rw [e, e', h, h', h'']
  omega


theorem and_mod_rd (m : Janus.Arm64.Memory) (a b : Nat) :
    (m.readLE a 8 &&& m.readLE b 8) % 18446744073709551616 = m.readLE a 8 &&& m.readLE b 8 :=
  Nat.mod_eq_of_lt (by simpa using (Nat.and_lt_two_pow _ (readLE8_lt _ _) : _ < 2 ^ 64))

theorem or_mod_rd (m : Janus.Arm64.Memory) (a b : Nat) :
    (m.readLE a 8 ||| m.readLE b 8) % 18446744073709551616 = m.readLE a 8 ||| m.readLE b 8 :=
  Nat.mod_eq_of_lt (by simpa using (Nat.or_lt_two_pow (readLE8_lt _ _) (readLE8_lt _ _) : _ < 2 ^ 64))

theorem xor_mod_rd (m : Janus.Arm64.Memory) (a b : Nat) :
    (m.readLE a 8 ^^^ m.readLE b 8) % 18446744073709551616 = m.readLE a 8 ^^^ m.readLE b 8 :=
  Nat.mod_eq_of_lt (by simpa using (Nat.xor_lt_two_pow (readLE8_lt _ _) (readLE8_lt _ _) : _ < 2 ^ 64))


@[simp] theorem readLE8_mod (m : Janus.Arm64.Memory) (a : Nat) :
    m.readLE a 8 % 18446744073709551616 = m.readLE a 8 := Nat.mod_eq_of_lt (readLE8_lt m a)


theorem dec_toNat (p : Prop) [Decidable p] :
    ((decide p).toNat = 1 ∧ p) ∨ ((decide p).toNat = 0 ∧ ¬ p) := by
  by_cases h : p <;> simp [h]

/-- the borrow chain of a 256-bit subtraction decides `<` (one limb at a time, as `SUB`/`SBB`/`SBB`/`SBB` compute it). -/
theorem lt_chain (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (h3 : a3 < 18446744073709551616) (g0 : b0 < 18446744073709551616)
    (g1 : b1 < 18446744073709551616) (g2 : b2 < 18446744073709551616) (g3 : b3 < 18446744073709551616) :
    decide (a3 < b3 + (decide (a2 < b2 + (decide (a1 < b1 + (decide (a0 < b0)).toNat)).toNat)).toNat) =
    decide (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3 <
      b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3) := by
  have e0 := dec_toNat (a0 < b0)
  have e1 := dec_toNat (a1 < b1 + (decide (a0 < b0)).toNat)
  have e2 := dec_toNat (a2 < b2 + (decide (a1 < b1 + (decide (a0 < b0)).toNat)).toNat)
  simp only [decide_eq_decide]
  omega


theorem lt_ite (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (h3 : a3 < 18446744073709551616) (g0 : b0 < 18446744073709551616)
    (g1 : b1 < 18446744073709551616) (g2 : b2 < 18446744073709551616) (g3 : b3 < 18446744073709551616) :
    (if (if a3 < b3 + (decide (a2 < b2 + (decide (a1 < b1 + (decide (a0 < b0)).toNat)).toNat)).toNat
          then 1#64 else 0#64).toNat = 0 then 0#8 else 1#8).toNat =
    (decide (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3 <
      b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3)).toNat := by
  have key := lt_chain a0 a1 a2 a3 b0 b1 b2 b3 h0 h1 h2 h3 g0 g1 g2 g3
  by_cases hP : a3 < b3 + (decide (a2 < b2 + (decide (a1 < b1 + (decide (a0 < b0)).toNat)).toNat)).toNat
  · rw [if_pos hP]
    simp only [hP, decide_true] at key
    have hQ := of_decide_eq_true key.symm
    simp [hQ]
  · rw [if_neg hP]
    simp only [hP, decide_false] at key
    have hQ := of_decide_eq_false key.symm
    simp [hQ]


theorem beq_toNat (a b : Nat) : (a == b).toNat = if a = b then 1 else 0 := by
  by_cases h : a = b <;> simp [h]

end Fv256.Util
