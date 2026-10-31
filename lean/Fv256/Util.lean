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
  let mut ps := collectDecToNat (← instantiateMVars (← getMainTarget)) #[]
  for d in ← getLCtx do
    if !d.isImplementationDetail then ps := collectDecToNat (← instantiateMVars d.type) ps
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



theorem carry4 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (h3 : a3 < 18446744073709551616) (g0 : b0 < 18446744073709551616)
    (g1 : b1 < 18446744073709551616) (g2 : b2 < 18446744073709551616) (g3 : b3 < 18446744073709551616) :
    (a3 + b3 + (a2 + b2 + (a1 + b1 + (a0 + b0) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616 =
    if 115792089237316195423570985008687907853269984665640564039457584007913129639936 ≤
      (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3) +
      (b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3) then 1 else 0 := by
  obtain ⟨k0, hk0⟩ : ∃ k, k = (a0 + b0) / 18446744073709551616 := ⟨_, rfl⟩
  obtain ⟨k1, hk1⟩ : ∃ k, k = (a1 + b1 + k0) / 18446744073709551616 := ⟨_, rfl⟩
  obtain ⟨k2, hk2⟩ : ∃ k, k = (a2 + b2 + k1) / 18446744073709551616 := ⟨_, rfl⟩
  rw [← hk0, ← hk1, ← hk2]
  split <;> omega


theorem add_out_iff (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (h3 : a3 < 18446744073709551616) (g0 : b0 < 18446744073709551616)
    (g1 : b1 < 18446744073709551616) (g2 : b2 < 18446744073709551616) (g3 : b3 < 18446744073709551616) :
    (18446744073709551616 ≤ a3 + b3 + (decide (18446744073709551616 ≤ a2 + b2 + (decide (18446744073709551616 ≤ a1 + b1 + (decide (18446744073709551616 ≤ a0 + b0)).toNat)).toNat)).toNat) ↔
    (115792089237316195423570985008687907853269984665640564039457584007913129639936 ≤
      (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3) +
      (b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3)) := by
  have e0 := dec_toNat (18446744073709551616 ≤ a0 + b0)
  have e1 := dec_toNat (18446744073709551616 ≤ a1 + b1 + (decide (18446744073709551616 ≤ a0 + b0)).toNat)
  have e2 := dec_toNat (18446744073709551616 ≤ a2 + b2 + (decide (18446744073709551616 ≤ a1 + b1 + (decide (18446744073709551616 ≤ a0 + b0)).toNat)).toNat)
  omega

open Lean Elab Tactic Meta in
/-- Like `dec_facts` but only for the goal (not the hypotheses). -/
elab "dec_goal" : tactic => withMainContext do
  let ps := collectDecToNat (← instantiateMVars (← getMainTarget)) #[]
  for p in ps do
    evalTactic (← `(tactic| have := Fv256.Util.dec_toNat $(← Term.exprToSyntax p)))

theorem lt_out_iff (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (h3 : a3 < 18446744073709551616) (g0 : b0 < 18446744073709551616)
    (g1 : b1 < 18446744073709551616) (g2 : b2 < 18446744073709551616) (g3 : b3 < 18446744073709551616) :
    (a3 < b3 + (decide (a2 < b2 + (decide (a1 < b1 + (decide (a0 < b0)).toNat)).toNat)).toNat) ↔
    (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3 <
      b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3) := by
  have := lt_chain a0 a1 a2 a3 b0 b1 b2 b3 h0 h1 h2 h3 g0 g1 g2 g3
  simpa [decide_eq_decide] using this


/-- signed `<` on four 64-bit limbs: sign bits first, then unsigned comparison. -/
theorem slt_iff (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (h3 : a3 < 18446744073709551616) (g0 : b0 < 18446744073709551616)
    (g1 : b1 < 18446744073709551616) (g2 : b2 < 18446744073709551616) (g3 : b3 < 18446744073709551616) :
    Spec.slt (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3)
      (b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3) = true ↔
    ((9223372036854775808 ≤ a3 ∧ b3 < 9223372036854775808) ∨
      ((a3 < 9223372036854775808 ↔ b3 < 9223372036854775808) ∧
        (a3 < b3 + (decide (a2 < b2 + (decide (a1 < b1 + (decide (a0 < b0)).toNat)).toNat)).toNat))) := by
  have hl := lt_out_iff a0 a1 a2 a3 b0 b1 b2 b3 h0 h1 h2 h3 g0 g1 g2 g3
  have hA : (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3) < 2 ^ 255 ↔ a3 < 9223372036854775808 := by
    omega
  have hB : (b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3) < 2 ^ 255 ↔ b3 < 9223372036854775808 := by
    omega
  have hA' : (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3) < 2 ^ 256 := by omega
  have hB' : (b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3) < 2 ^ 256 := by omega
  rw [hl, ← hA, ← hB]
  generalize (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3) = A at *
  generalize (b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3) = B at *
  unfold Spec.slt Spec.signed
  simp only [decide_eq_true_eq]
  split <;> split <;> omega


theorem slt_toNat (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (h3 : a3 < 18446744073709551616) (g0 : b0 < 18446744073709551616)
    (g1 : b1 < 18446744073709551616) (g2 : b2 < 18446744073709551616) (g3 : b3 < 18446744073709551616) :
    (Spec.slt (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3)
      (b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3)).toNat =
    (decide ((9223372036854775808 ≤ a3 ∧ b3 < 9223372036854775808) ∨
      ((a3 < 9223372036854775808 ↔ b3 < 9223372036854775808) ∧
        (a3 < b3 + (decide (a2 < b2 + (decide (a1 < b1 + (decide (a0 < b0)).toNat)).toNat)).toNat)))).toNat := by
  have := slt_iff a0 a1 a2 a3 b0 b1 b2 b3 h0 h1 h2 h3 g0 g1 g2 g3
  by_cases hc : Spec.slt (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3)
      (b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3) = true
  · rw [hc]; have := this.mp hc; simp [this]
  · have h' : ¬ (_ : Prop) := fun h => hc (this.mpr h)
    simp only [Bool.not_eq_true] at hc
    rw [hc]; simp [h']


theorem sgt_toNat (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (h3 : a3 < 18446744073709551616) (g0 : b0 < 18446744073709551616)
    (g1 : b1 < 18446744073709551616) (g2 : b2 < 18446744073709551616) (g3 : b3 < 18446744073709551616) :
    (Spec.sgt (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3)
      (b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3)).toNat =
    (decide ((9223372036854775808 ≤ b3 ∧ a3 < 9223372036854775808) ∨
      ((b3 < 9223372036854775808 ↔ a3 < 9223372036854775808) ∧
        (b3 < a3 + (decide (b2 < a2 + (decide (b1 < a1 + (decide (b0 < a0)).toNat)).toNat)).toNat)))).toNat :=
  slt_toNat b0 b1 b2 b3 a0 a1 a2 a3 g0 g1 g2 g3 h0 h1 h2 h3


theorem cmp_ofInt (A B : Nat) :
    BitVec.ofInt 64 (Spec.cmp A B) =
      if A < B then 18446744073709551615#64 else if A = B then 0#64 else 1#64 := by
  unfold Spec.cmp
  by_cases h1 : A < B
  · simp [h1]
  · by_cases h2 : A = B
    · simp [h1, h2]
    · simp [h1, h2]


theorem ite_one_toNat (P : Prop) [Decidable P] : (if P then 1#64 else 0#64).toNat = (decide P).toNat := by
  by_cases h : P <;> simp [h]


theorem ite01_eq1 (P : Prop) [Decidable P] : ((if P then 0 else 1 : Nat) = 1) ↔ ¬P := by
  by_cases h : P <;> simp [h]
theorem ite01_eq0 (P : Prop) [Decidable P] : ((if P then 0 else 1 : Nat) = 0) ↔ P := by
  by_cases h : P <;> simp [h]


theorem zero4_iff (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (h3 : a3 < 18446744073709551616) (g0 : b0 < 18446744073709551616)
    (g1 : b1 < 18446744073709551616) (g2 : b2 < 18446744073709551616) (g3 : b3 < 18446744073709551616) :
    (((a3 + (18446744073709551616 - 1 - b3) +
          (a2 + (18446744073709551616 - 1 - b2) +
              (a1 + (18446744073709551616 - 1 - b1) + (decide (b0 ≤ a0)).toNat) / 18446744073709551616) /
            18446744073709551616) % 18446744073709551616 = 0 ∧
      ((18446744073709551616 - b0 + a0) % 18446744073709551616 = 0 ∧
        (a1 + (18446744073709551616 - 1 - b1) + (decide (b0 ≤ a0)).toNat) % 18446744073709551616 = 0) ∧
      (a2 + (18446744073709551616 - 1 - b2) +
          (a1 + (18446744073709551616 - 1 - b1) + (decide (b0 ≤ a0)).toNat) / 18446744073709551616) %
        18446744073709551616 = 0)) ↔
    (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3 =
      b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3) := by
  obtain ⟨c, hc⟩ : ∃ c, c = (decide (b0 ≤ a0)).toNat := ⟨_, rfl⟩
  have hc2 : (c = 1 ∧ b0 ≤ a0) ∨ (c = 0 ∧ ¬ b0 ≤ a0) := by rw [hc]; exact dec_toNat _
  rw [← hc]
  obtain ⟨k1, hk1⟩ : ∃ k, k = (a1 + (18446744073709551616 - 1 - b1) + c) / 18446744073709551616 := ⟨_, rfl⟩
  obtain ⟨k2, hk2⟩ : ∃ k, k = (a2 + (18446744073709551616 - 1 - b2) + k1) / 18446744073709551616 := ⟨_, rfl⟩
  rw [← hk1, ← hk2]
  omega

theorem msb_m1 : (18446744073709551615#64).msb = true := by decide
theorem msb_0 : (0#64).msb = false := by decide
theorem msb_1 : (1#64).msb = false := by decide


/-- `m'` agrees with `m` and has the same regions outside two byte ranges `[p, p+n)` and `[q, q+k)`:
the result object and a callee's scratch (spill) slots below the stack pointer. -/
def OnlyWrites2 (m m' : Janus.Arm64.Memory) (p n q k : Nat) : Prop :=
  m'.regions = m.regions ∧ ∀ a, (a < p ∨ p + n ≤ a) → (a < q ∨ q + k ≤ a) → m'.bytes a = m.bytes a

theorem ow2_refl (m : Janus.Arm64.Memory) (p n q k : Nat) : OnlyWrites2 m m p n q k := ⟨rfl, fun _ _ _ => rfl⟩

theorem ow2_wl {m m' : Janus.Arm64.Memory} {p n q k a j : Nat} (v : Nat) (h : OnlyWrites2 m m' p n q k)
    (h1 : p ≤ a) (h2 : a + j ≤ p + n) : OnlyWrites2 m (m'.writeLE a j v) p n q k :=
  ⟨by rw [Janus.Arm64.Memory.regions_writeLE]; exact h.1, fun b hb hb' => by
    rw [Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]; exact h.2 b hb hb'⟩

theorem ow2_wr {m m' : Janus.Arm64.Memory} {p n q k a j : Nat} (v : Nat) (h : OnlyWrites2 m m' p n q k)
    (h1 : q ≤ a) (h2 : a + j ≤ q + k) : OnlyWrites2 m (m'.writeLE a j v) p n q k :=
  ⟨by rw [Janus.Arm64.Memory.regions_writeLE]; exact h.1, fun b hb hb' => by
    rw [Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]; exact h.2 b hb hb'⟩

theorem ow2_wl_iff {m m' : Janus.Arm64.Memory} {p n q k a j : Nat} (v : Nat)
    (h1 : p ≤ a) (h2 : a + j ≤ p + n) :
    OnlyWrites2 m (m'.writeLE a j v) p n q k ↔ OnlyWrites2 m m' p n q k :=
  ⟨fun h => ⟨by rw [← Janus.Arm64.Memory.regions_writeLE m' a j v]; exact h.1, fun b hb hb' => by
      rw [← h.2 b hb hb', Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]⟩,
   fun h => ow2_wl v h h1 h2⟩

theorem ow2_wr_iff {m m' : Janus.Arm64.Memory} {p n q k a j : Nat} (v : Nat)
    (h1 : q ≤ a) (h2 : a + j ≤ q + k) :
    OnlyWrites2 m (m'.writeLE a j v) p n q k ↔ OnlyWrites2 m m' p n q k :=
  ⟨fun h => ⟨by rw [← Janus.Arm64.Memory.regions_writeLE m' a j v]; exact h.1, fun b hb hb' => by
      rw [← h.2 b hb hb', Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]⟩,
   fun h => ow2_wr v h h1 h2⟩

theorem ow2_self_iff (m : Janus.Arm64.Memory) (p n q k : Nat) : OnlyWrites2 m m p n q k ↔ True :=
  ⟨fun _ => trivial, fun _ => ow2_refl m p n q k⟩

theorem clz_bl (n x : Nat) (hx : x < 2 ^ n) : Janus.Arm64.clzNat n x + Spec.bitLen x = n := by
  induction n generalizing x with
  | zero =>
    have : x = 0 := by simpa using hx
    subst this; simp [Janus.Arm64.clzNat, Spec.bitLen]
  | succ n ih =>
    unfold Janus.Arm64.clzNat
    by_cases hb : x.testBit n = true
    · have h1 : 2 ^ n ≤ x := Nat.ge_two_pow_of_testBit hb
      have h2 : Nat.log2 x = n := by
        rw [Nat.log2_eq_iff (by omega)]; exact ⟨h1, by simpa [Nat.pow_succ] using hx⟩
      simp [hb, Spec.bitLen, h2]; omega
    · have hb' : x.testBit n = false := by simpa using hb
      have h3 : x < 2 ^ n := by
        refine Classical.byContradiction fun hc => ?_
        have h1 : 2 ^ n ≤ x := by omega
        apply hb
        rw [Nat.testBit_eq_decide_div_mod_eq]
        have hd : x / 2 ^ n = 1 := Nat.div_eq_of_lt_le (by omega) (by rw [Nat.pow_succ] at hx; omega)
        simp [hd]
      simp only [hb', Bool.false_eq_true, ite_false]
      have := ih x h3
      omega

theorem bl_split (k a c : Nat) (ha : a < 2 ^ k) : Spec.bitLen (a + 2 ^ k * c) = if c = 0 then Spec.bitLen a else k + Spec.bitLen c := by
  by_cases hc : c = 0
  · simp [hc]
  · have hP : 0 < 2 ^ k := Nat.two_pow_pos k
    have hm := (Nat.log2_eq_iff hc).mp rfl
    obtain ⟨m1, m2⟩ := hm
    have e1 : 2 ^ k * 2 ^ Nat.log2 c ≤ 2 ^ k * c := Nat.mul_le_mul_left _ m1
    have e2 : 2 ^ k * (c + 1) ≤ 2 ^ k * 2 ^ (Nat.log2 c + 1) := Nat.mul_le_mul_left _ m2
    have hne : a + 2 ^ k * c ≠ 0 := by
      have : 0 < 2 ^ k * c := Nat.mul_pos hP (Nat.pos_of_ne_zero hc)
      omega
    have : Nat.log2 (a + 2 ^ k * c) = k + Nat.log2 c := by
      rw [Nat.log2_eq_iff hne]
      constructor
      · rw [Nat.pow_add]; omega
      · rw [show k + Nat.log2 c + 1 = k + (Nat.log2 c + 1) from by omega, Nat.pow_add]
        rw [Nat.mul_add] at e2; omega
    unfold Spec.bitLen; rw [if_neg hne, if_neg hc, this]; rw [if_neg hc]; omega

theorem bl_4 (a0 a1 a2 a3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) :
    Spec.bitLen (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3) =
    if a3 ≠ 0 then 192 + Spec.bitLen a3 else if a2 ≠ 0 then 128 + Spec.bitLen a2 else if a1 ≠ 0 then 64 + Spec.bitLen a1 else Spec.bitLen a0 := by
  have e : a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3 =
      (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2) + 2 ^ 192 * a3 := by omega
  have l1 : a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 < 2 ^ 192 := by omega
  have s1 := bl_split 192 _ a3 l1
  have l2 : a0 + 2 ^ 64 * a1 < 2 ^ 128 := by omega
  have s2 := bl_split 128 _ a2 l2
  have s3 := bl_split 64 a0 a1 (by omega)
  rw [e, s1]
  by_cases c3 : a3 = 0
  · simp only [c3, if_true]
    rw [show a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 = (a0 + 2 ^ 64 * a1) + 2 ^ 128 * a2 by omega, s2]
    by_cases c2 : a2 = 0
    · simp only [c2, if_true]; rw [s3]; simp
    · simp [c2]
  · simp [c3]


theorem bl_3 (a0 a1 a2 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616) (h2 : a2 < 18446744073709551616) :
    Spec.bitLen (a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2) =
    if a2 ≠ 0 then 128 + Spec.bitLen a2 else if a1 ≠ 0 then 64 + Spec.bitLen a1 else Spec.bitLen a0 := by
  have := bl_4 a0 a1 a2 0 h0 h1 h2
  simpa using this

theorem bl_2 (a0 a1 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616) :
    Spec.bitLen (a0 + 18446744073709551616 * a1) =
    if a1 ≠ 0 then 64 + Spec.bitLen a1 else Spec.bitLen a0 := by
  have := bl_3 a0 a1 0 h0 h1 (by decide)
  simpa using this


section BEsec
open Janus.Arm64

theorem fromBE_add (f : Nat → Nat) (m n : Nat) :
    Spec.fromBE f (m + n) = Spec.fromBE f m * 256 ^ n + Spec.fromBE (fun i => f (m + i)) n := by
  induction m generalizing f with
  | zero => simp [Spec.fromBE]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [Spec.fromBE]
    rw [ih (fun i => f (i + 1))]
    have e : (fun i => f (m + i + 1)) = fun i => f (m + 1 + i) :=
      funext fun i => by rw [show m + i + 1 = m + 1 + i by omega]
    simp only [e]
    rw [Nat.pow_add, Nat.add_mul, Nat.mul_assoc]
    omega

theorem revBytes_readLE (m : Memory) (a k : Nat) :
    revBytesNat k (m.readLE a k) = Spec.fromBE (fun i => m.readLE (a + i) 1) k := by
  induction k generalizing a with
  | zero => simp [revBytesNat, Spec.fromBE]
  | succ k ih =>
    rw [Memory.readLE_succ, revBytesNat]
    have h1 : ((m.bytes a).toNat + 256 * m.readLE (a + 1) k) % 256 = (m.bytes a).toNat := by
      have := (m.bytes a).isLt
      omega
    have h2 : ((m.bytes a).toNat + 256 * m.readLE (a + 1) k) / 256 = m.readLE (a + 1) k := by
      have := (m.bytes a).isLt
      omega
    rw [h1, h2, ih (a + 1)]
    simp only [Spec.fromBE, Nat.add_zero, Memory.readLE_one]
    have e : (fun i => (m.bytes (a + 1 + i)).toNat) = fun i => (m.bytes (a + (i + 1))).toNat :=
      funext fun i => by rw [show a + 1 + i = a + (i + 1) by omega]
    rw [e]

theorem be32_rev (m : Memory) (p : Nat) :
    Spec.fromBE (fun i => m.readLE (p + i) 1) 32 =
      revBytesNat 8 (m.readLE p 8) * 2 ^ 192 + revBytesNat 8 (m.readLE (p + 8) 8) * 2 ^ 128 +
        revBytesNat 8 (m.readLE (p + 16) 8) * 2 ^ 64 + revBytesNat 8 (m.readLE (p + 24) 8) := by
  have h : ∀ q, Spec.fromBE (fun i => m.readLE (p + (q + i)) 1) 8 = revBytesNat 8 (m.readLE (p + q) 8) := by
    intro q
    rw [revBytes_readLE]
    simp only [Nat.add_assoc]
  have e0 : Spec.fromBE (fun i => m.readLE (p + i) 1) 8 = revBytesNat 8 (m.readLE p 8) :=
    revBytes_readLE m p 8 ▸ rfl
  rw [show 32 = 8 + 24 from rfl, fromBE_add, show 24 = 8 + 16 from rfl, fromBE_add, show 16 = 8 + 8 from rfl, fromBE_add]
  have h2 := h (8 + 8)
  have h3 := h (8 + (8 + 8))
  simp only [Nat.add_assoc] at h2 h3
  rw [e0, h 8, h2, h3]
  simp only [Nat.reduceAdd, Nat.reducePow, Nat.add_mul]
  omega

theorem revBytes_lt (k x : Nat) : revBytesNat k x < 256 ^ k := by
  induction k generalizing x with
  | zero => simp [revBytesNat]
  | succ k ih =>
    unfold revBytesNat
    have h1 : x % 256 < 256 := Nat.mod_lt _ (by decide)
    have h2 := ih (x / 256)
    rw [Nat.pow_succ]
    have : (x % 256) * 256 ^ k + revBytesNat k (x / 256) < 256 * 256 ^ k := by
      have : (x % 256) * 256 ^ k ≤ 255 * 256 ^ k := Nat.mul_le_mul_right _ (by omega)
      omega
    omega

theorem rc_rev8 (v : Nat) (hv : v < 18446744073709551616) :
    revContainersNat 8 1 v % 18446744073709551616 = revBytesNat 8 v := by
  have h := revBytes_lt 8 v
  simp only [revContainersNat, Nat.reducePow, Nat.mod_eq_of_lt hv] at *
  omega

end BEsec

end Fv256.Util
