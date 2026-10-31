import Janus
import Fv256.Spec

open Lean Elab Tactic Meta in
/-- collect the propositions `p` of every `(decide p).toNat` in an expression -/
partial def collectDecToNat (e : Expr) (acc : Array Expr) : Array Expr :=
  match e with
  | .app f a =>
    let acc := collectDecToNat f (collectDecToNat a acc)
    if e.isAppOfArity ``Bool.toNat 1 then
      match a.getAppFnArgs with
      | (``Decidable.decide, #[p, _]) => if acc.contains p then acc else acc.push p
      | _ => acc
    else acc
  | .lam _ t b _ | .forallE _ t b _ => collectDecToNat b (collectDecToNat t acc)
  | .mdata _ b => collectDecToNat b acc
  | _ => acc

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


theorem subFlags_fst_toNat (x y : BitVec 64) (b : Bool) :
    (Janus.Amd64.subFlags x y b).1.toNat = (x.toNat + 2 ^ 64 - y.toNat - b.toNat) % 2 ^ 64 := by
  simp [Janus.Amd64.subFlags]

theorem addFlags_fst_toNat (x y : BitVec 64) (b : Bool) :
    (Janus.Amd64.addFlags x y b).1.toNat = (x.toNat + y.toNat + b.toNat) % 2 ^ 64 := by
  simp [Janus.Amd64.addFlags]


open Janus.Amd64 in
theorem neg_chain (x0 x1 x2 x3 : Nat) (h0 : x0 < 18446744073709551616) (h1 : x1 < 18446744073709551616)
    (h2 : x2 < 18446744073709551616) (h3 : x3 < 18446744073709551616) :
    (18446744073709551616 - x0) % 18446744073709551616 +
            18446744073709551616 *
              (subFlags (0#64) (BitVec.ofNat 64 x1) (decide (0 < x0))).fst.toNat +
          340282366920938463463374607431768211456 *
            (subFlags (0#64) (BitVec.ofNat 64 x2) (decide (0 < x1 + (decide (0 < x0)).toNat))).fst.toNat +
        6277101735386680763835789423207666416102355444464034512896 *
          (subFlags (0#64) (BitVec.ofNat 64 x3)
                (decide (0 < x2 + (decide (0 < x1 + (decide (0 < x0)).toNat)).toNat))).fst.toNat =
    (115792089237316195423570985008687907853269984665640564039457584007913129639936 - (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 +
        6277101735386680763835789423207666416102355444464034512896 * x3)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  have e0 := dec_toNat (0 < x0)
  have e1 := dec_toNat (0 < x1 + (decide (0 < x0)).toNat)
  have e2 := dec_toNat (0 < x2 + (decide (0 < x1 + (decide (0 < x0)).toNat)).toNat)
  simp only [subFlags_fst_toNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3]
  omega


theorem add_chain (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (h3 : a3 < 18446744073709551616) (g0 : b0 < 18446744073709551616)
    (g1 : b1 < 18446744073709551616) (g2 : b2 < 18446744073709551616) (g3 : b3 < 18446744073709551616) :
    (a0 + b0) % 18446744073709551616 +
        18446744073709551616 * ((a1 + b1 + (decide (18446744073709551616 ≤ a0 + b0)).toNat) % 18446744073709551616) +
      340282366920938463463374607431768211456 * ((a2 + b2 + (decide (18446744073709551616 ≤ a1 + b1 + (decide (18446744073709551616 ≤ a0 + b0)).toNat)).toNat) % 18446744073709551616) +
    6277101735386680763835789423207666416102355444464034512896 * ((a3 + b3 + (decide (18446744073709551616 ≤ a2 + b2 + (decide (18446744073709551616 ≤ a1 + b1 + (decide (18446744073709551616 ≤ a0 + b0)).toNat)).toNat)).toNat) % 18446744073709551616) =
    ((a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3) +
     (b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3)) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  have e0 := dec_toNat (18446744073709551616 ≤ a0 + b0)
  have e1 := dec_toNat (18446744073709551616 ≤ a1 + b1 + (decide (18446744073709551616 ≤ a0 + b0)).toNat)
  have e2 := dec_toNat (18446744073709551616 ≤ a2 + b2 + (decide (18446744073709551616 ≤ a1 + b1 + (decide (18446744073709551616 ≤ a0 + b0)).toNat)).toNat)
  omega


open Lean Elab Tactic Meta in
/-- For every `(decide p).toNat` in the goal add the fact `dec_toNat p` (the value is 1 and `p`, or 0 and `¬p`), so that
`omega` can reason about carries without a case split. -/
elab "dec_facts" : tactic => withMainContext do
  let ps := collectDecToNat (← instantiateMVars (← getMainTarget)) #[]
  for p in ps do
    evalTactic (← `(tactic| have := Fv256.Util.dec_toNat $(← Term.exprToSyntax p)))


theorem sign_zero (S : Nat) (h : S = 0) : BitVec.ofInt 64 (Spec.sign S) = 0#64 := by
  simp [Spec.sign, h]

theorem sign_pos (S : Nat) (h : S ≠ 0) (h2 : S < 2 ^ 255) : BitVec.ofInt 64 (Spec.sign S) = 1#64 := by
  simp [Spec.sign, h, h2]

theorem sign_neg (S : Nat) (h : 2 ^ 255 ≤ S) : BitVec.ofInt 64 (Spec.sign S) = 18446744073709551615#64 := by
  have h0 : S ≠ 0 := by have : 0 < 2 ^ 255 := by decide
                        omega
  have h1 : ¬ S < 2 ^ 255 := by omega
  simp [Spec.sign, h0, h1]

theorem borrow4_gen (a0 a1 a2 a3 b0 b1 b2 b3 c : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (h3 : a3 < 18446744073709551616) (g0 : b0 < 18446744073709551616)
    (g1 : b1 < 18446744073709551616) (g2 : b2 < 18446744073709551616) (g3 : b3 < 18446744073709551616)
    (hc : (c = 1 ∧ b0 ≤ a0) ∨ (c = 0 ∧ ¬ b0 ≤ a0)) :
    ((18446744073709551616 -
          (18446744073709551615 +
              (a3 + (18446744073709551616 - 1 - b3) +
                  (a2 + (18446744073709551616 - 1 - b2) +
                      (a1 + (18446744073709551616 - 1 - b1) + c) / 18446744073709551616) /
                    18446744073709551616) /
                18446744073709551616) %
            18446744073709551616) %
        18446744073709551616 = 0) ↔
    (b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3 ≤
      a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3) := by
  obtain ⟨k1, hk1⟩ : ∃ k, k = (a1 + (18446744073709551616 - 1 - b1) + c) / 18446744073709551616 := ⟨_, rfl⟩
  obtain ⟨k2, hk2⟩ : ∃ k, k = (a2 + (18446744073709551616 - 1 - b2) + k1) / 18446744073709551616 := ⟨_, rfl⟩
  obtain ⟨k3, hk3⟩ : ∃ k, k = (a3 + (18446744073709551616 - 1 - b3) + k2) / 18446744073709551616 := ⟨_, rfl⟩
  rw [← hk1, ← hk2, ← hk3]
  omega

theorem borrow4 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (h3 : a3 < 18446744073709551616) (g0 : b0 < 18446744073709551616)
    (g1 : b1 < 18446744073709551616) (g2 : b2 < 18446744073709551616) (g3 : b3 < 18446744073709551616) :
    (b0 ≤ a0 → (((18446744073709551616 -
          (18446744073709551615 +
              (a3 + (18446744073709551616 - 1 - b3) +
                  (a2 + (18446744073709551616 - 1 - b2) +
                      (a1 + (18446744073709551616 - 1 - b1) + 1) / 18446744073709551616) /
                    18446744073709551616) /
                18446744073709551616) %
            18446744073709551616) %
        18446744073709551616 = 0) ↔
    (b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3 ≤
      a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3))) ∧
    (¬ b0 ≤ a0 → (((18446744073709551616 -
          (18446744073709551615 +
              (a3 + (18446744073709551616 - 1 - b3) +
                  (a2 + (18446744073709551616 - 1 - b2) +
                      (a1 + (18446744073709551616 - 1 - b1) + 0) / 18446744073709551616) /
                    18446744073709551616) /
                18446744073709551616) %
            18446744073709551616) %
        18446744073709551616 = 0) ↔
    (b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3 ≤
      a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3))) :=
  ⟨fun h => borrow4_gen a0 a1 a2 a3 b0 b1 b2 b3 1 h0 h1 h2 h3 g0 g1 g2 g3 (Or.inl ⟨rfl, h⟩),
   fun h => borrow4_gen a0 a1 a2 a3 b0 b1 b2 b3 0 h0 h1 h2 h3 g0 g1 g2 g3 (Or.inr ⟨rfl, h⟩)⟩


theorem borrow4_eq1 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (h3 : a3 < 18446744073709551616) (g0 : b0 < 18446744073709551616)
    (g1 : b1 < 18446744073709551616) (g2 : b2 < 18446744073709551616) (g3 : b3 < 18446744073709551616)
    (hc : b0 ≤ a0) : (18446744073709551616 -
          (18446744073709551615 +
              (a3 + (18446744073709551616 - 1 - b3) +
                  (a2 + (18446744073709551616 - 1 - b2) +
                      (a1 + (18446744073709551616 - 1 - b1) + 1) / 18446744073709551616) /
                    18446744073709551616) /
                18446744073709551616) %
            18446744073709551616) %
        18446744073709551616 = (if b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3 ≤
      a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3 then 0 else 1) := by
  obtain ⟨k1, hk1⟩ : ∃ k, k = (a1 + (18446744073709551616 - 1 - b1) + 1) / 18446744073709551616 := ⟨_, rfl⟩
  obtain ⟨k2, hk2⟩ : ∃ k, k = (a2 + (18446744073709551616 - 1 - b2) + k1) / 18446744073709551616 := ⟨_, rfl⟩
  obtain ⟨k3, hk3⟩ : ∃ k, k = (a3 + (18446744073709551616 - 1 - b3) + k2) / 18446744073709551616 := ⟨_, rfl⟩
  rw [← hk1, ← hk2, ← hk3]
  split <;> omega

theorem borrow4_eq0 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (h3 : a3 < 18446744073709551616) (g0 : b0 < 18446744073709551616)
    (g1 : b1 < 18446744073709551616) (g2 : b2 < 18446744073709551616) (g3 : b3 < 18446744073709551616)
    (hc : ¬ b0 ≤ a0) : (18446744073709551616 -
          (18446744073709551615 +
              (a3 + (18446744073709551616 - 1 - b3) +
                  (a2 + (18446744073709551616 - 1 - b2) +
                      (a1 + (18446744073709551616 - 1 - b1) + 0) / 18446744073709551616) /
                    18446744073709551616) /
                18446744073709551616) %
            18446744073709551616) %
        18446744073709551616 = (if b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3 ≤
      a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3 then 0 else 1) := by
  obtain ⟨k1, hk1⟩ : ∃ k, k = (a1 + (18446744073709551616 - 1 - b1) + 0) / 18446744073709551616 := ⟨_, rfl⟩
  obtain ⟨k2, hk2⟩ : ∃ k, k = (a2 + (18446744073709551616 - 1 - b2) + k1) / 18446744073709551616 := ⟨_, rfl⟩
  obtain ⟨k3, hk3⟩ : ∃ k, k = (a3 + (18446744073709551616 - 1 - b3) + k2) / 18446744073709551616 := ⟨_, rfl⟩
  rw [← hk1, ← hk2, ← hk3]
  split <;> omega


theorem borrow4_dec (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (h3 : a3 < 18446744073709551616) (g0 : b0 < 18446744073709551616)
    (g1 : b1 < 18446744073709551616) (g2 : b2 < 18446744073709551616) (g3 : b3 < 18446744073709551616) :
    (18446744073709551616 -
          (18446744073709551615 +
              (a3 + (18446744073709551616 - 1 - b3) +
                  (a2 + (18446744073709551616 - 1 - b2) +
                      (a1 + (18446744073709551616 - 1 - b1) + (decide (b0 ≤ a0)).toNat) / 18446744073709551616) /
                    18446744073709551616) /
                18446744073709551616) %
            18446744073709551616) %
        18446744073709551616 = (if b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3 ≤
      a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3 then 0 else 1) := by
  by_cases hc : b0 ≤ a0
  · simp only [hc, decide_true, Bool.toNat_true]
    exact borrow4_eq1 a0 a1 a2 a3 b0 b1 b2 b3 h0 h1 h2 h3 g0 g1 g2 g3 hc
  · simp only [hc, decide_false, Bool.toNat_false]
    exact borrow4_eq0 a0 a1 a2 a3 b0 b1 b2 b3 h0 h1 h2 h3 g0 g1 g2 g3 hc

theorem borrow4_dec' (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (h3 : a3 < 18446744073709551616) (g0 : b0 < 18446744073709551616)
    (g1 : b1 < 18446744073709551616) (g2 : b2 < 18446744073709551616) (g3 : b3 < 18446744073709551616) :
    (18446744073709551616 -
          (18446744073709551615 +
              (a3 + (18446744073709551615 - b3) +
                  (a2 + (18446744073709551615 - b2) +
                      (a1 + (18446744073709551615 - b1) + (decide (b0 ≤ a0)).toNat) / 18446744073709551616) /
                    18446744073709551616) /
                18446744073709551616) %
            18446744073709551616) %
        18446744073709551616 = (if b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3 ≤
      a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3 then 0 else 1) := by
  by_cases hc : b0 ≤ a0
  · simp only [hc, decide_true, Bool.toNat_true]
    have := borrow4_eq1 a0 a1 a2 a3 b0 b1 b2 b3 h0 h1 h2 h3 g0 g1 g2 g3 hc
    simpa [Nat.sub_sub, Nat.add_comm 1] using this
  · simp only [hc, decide_false, Bool.toNat_false]
    have := borrow4_eq0 a0 a1 a2 a3 b0 b1 b2 b3 h0 h1 h2 h3 g0 g1 g2 g3 hc
    simpa [Nat.sub_sub, Nat.add_comm 1] using this


end Fv256.Util
