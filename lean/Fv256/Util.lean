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

theorem chunk8 (m : Memory) (a : Nat) :
    revContainersNat 8 1 (m.readLE a 8) % 18446744073709551616 =
      Spec.fromBE (fun i => m.readLE (a + i) 1) 8 := by
  rw [rc_rev8 _ (readLE8_lt _ _), revBytes_readLE]

theorem chunk4 (m : Memory) (a : Nat) :
    (BitVec.setWidth 64 (BitVec.ofNat 32
      (revContainersNat 4 1 (BitVec.setWidth 32 (BitVec.ofNat 64 (m.readLE a 4))).toNat))).toNat =
      Spec.fromBE (fun i => m.readLE (a + i) 1) 4 := by
  have h4 : m.readLE a 4 < 4294967296 := by simpa using Memory.readLE_lt m a 4
  have hr := revBytes_lt 4 (m.readLE a 4)
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, revContainersNat]
  rw [← revBytes_readLE]
  simp only [Nat.reducePow] at hr
  have e1 : m.readLE a 4 % 18446744073709551616 % 4294967296 = m.readLE a 4 := by omega
  rw [e1]
  have e2 : revBytesNat 4 (m.readLE a 4 % 4294967296) = revBytesNat 4 (m.readLE a 4) := by
    rw [Nat.mod_eq_of_lt h4]
  omega

theorem rot0 {w : Nat} (x : BitVec w) : x.rotateRight 0 = x := by
  simp [BitVec.rotateRight, BitVec.rotateRightAux]

theorem chunk2 (m : Memory) (a : Nat) :
    ((BitVec.setWidth 64 (BitVec.ofNat 32
      (revContainersNat 2 2 (BitVec.setWidth 32 (BitVec.ofNat 64 (m.readLE a 2))).toNat))).rotateRight 0).toNat % 65536 =
      Spec.fromBE (fun i => m.readLE (a + i) 1) 2 := by
  have h2 : m.readLE a 2 < 65536 := by simpa using Memory.readLE_lt m a 2
  have hr := revBytes_lt 2 (m.readLE a 2)
  simp only [rot0, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, revContainersNat]
  rw [← revBytes_readLE]
  simp only [Nat.reducePow] at hr
  have e1 : m.readLE a 2 % 18446744073709551616 % 4294967296 = m.readLE a 2 := by omega
  rw [e1]
  have e2 : m.readLE a 2 % 65536 = m.readLE a 2 := Nat.mod_eq_of_lt h2
  have e3 : m.readLE a 2 / 65536 = 0 := by omega
  simp only [e2, e3, Nat.zero_mod, revBytesNat, Nat.mul_zero, Nat.add_zero]
  omega


theorem or_hi (a c k : Nat) (ha : a < 2 ^ k) : a ||| (c * 2 ^ k) = a + c * 2 ^ k := by
  have := or_split k a 0 0 c ha (Nat.two_pow_pos k)
  simpa [Nat.mul_comm] using this

theorem or_hi16 (a c : Nat) (ha : a < 65536) : a ||| (c * 65536) = a + c * 65536 := or_hi a c 16 ha
theorem or_hi24 (a c : Nat) (ha : a < 16777216) : a ||| (c * 16777216) = a + c * 16777216 := or_hi a c 24 ha
theorem or_hi32 (a c : Nat) (ha : a < 4294967296) : a ||| (c * 4294967296) = a + c * 4294967296 := or_hi a c 32 ha
theorem or_hi40 (a c : Nat) (ha : a < 1099511627776) : a ||| (c * 1099511627776) = a + c * 1099511627776 := or_hi a c 40 ha
theorem or_hi48 (a c : Nat) (ha : a < 281474976710656) : a ||| (c * 281474976710656) = a + c * 281474976710656 := or_hi a c 48 ha
theorem or_hi56 (a c : Nat) (ha : a < 72057594037927936) : a ||| (c * 72057594037927936) = a + c * 72057594037927936 := or_hi a c 56 ha

theorem rd1_lt (m : Memory) (a : Nat) : m.readLE a 1 < 256 := by simpa using Memory.readLE_lt m a 1

theorem rev_succ_top (k x : Nat) (hx : x < 256 ^ (k + 1)) :
    revBytesNat (k + 1) x = x / 256 ^ k + 256 * revBytesNat k (x % 256 ^ k) := by
  induction k generalizing x with
  | zero =>
    simp only [Nat.pow_zero, Nat.zero_add, Nat.pow_one] at hx
    simp [revBytesNat, Nat.mod_eq_of_lt hx]
  | succ k ih =>
    have hx' : x / 256 < 256 ^ (k + 1) := by
      rw [Nat.pow_succ] at hx
      omega
    rw [revBytesNat, ih (x / 256) hx']
    rw [show revBytesNat (k + 1) (x % 256 ^ (k + 1)) = (x % 256 ^ (k + 1) % 256) * 256 ^ k + revBytesNat k (x % 256 ^ (k + 1) / 256) from rfl]
    have e1 : x / 256 / 256 ^ k = x / 256 ^ (k + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    have e2 : x % 256 ^ (k + 1) % 256 = x % 256 := by
      rw [Nat.mod_mod_of_dvd]; exact ⟨256 ^ k, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    have e3 : x % 256 ^ (k + 1) / 256 = x / 256 % 256 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]
    rw [e1, e2, e3]
    have e4 : (x % 256) * 256 ^ (k + 1) = 256 * ((x % 256) * 256 ^ k) := by
      rw [Nat.pow_succ]; rw [Nat.mul_comm (256 ^ k) 256, ← Nat.mul_assoc, Nat.mul_comm (x % 256) 256, Nat.mul_assoc]
    rw [e4]
    omega

theorem rev_rev (k x : Nat) (hx : x < 256 ^ k) : revBytesNat k (revBytesNat k x) = x := by
  induction k generalizing x with
  | zero => simp at hx; simp [revBytesNat, hx]
  | succ k ih =>
    have hR := revBytes_lt k (x / 256)
    have hy : (x % 256) * 256 ^ k + revBytesNat k (x / 256) < 256 ^ (k + 1) := by
      have : (x % 256) * 256 ^ k ≤ 255 * 256 ^ k := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.pow_succ]; omega
    have hxb : x / 256 < 256 ^ k := by rw [Nat.pow_succ] at hx; omega
    rw [show revBytesNat (k + 1) x = (x % 256) * 256 ^ k + revBytesNat k (x / 256) from rfl]
    rw [rev_succ_top k _ hy]
    have e1 : ((x % 256) * 256 ^ k + revBytesNat k (x / 256)) / 256 ^ k = x % 256 := by
      have hp : 0 < 256 ^ k := Nat.pos_of_ne_zero (fun h => by simp at h)
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hR]; simp
    have e2 : ((x % 256) * 256 ^ k + revBytesNat k (x / 256)) % 256 ^ k = revBytesNat k (x / 256) := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hR]
    rw [e1, e2, ih _ hxb]
    omega
theorem rev8_rev8 (x : Nat) (hx : x < 18446744073709551616) : revBytesNat 8 (revBytesNat 8 x) = x :=
  rev_rev 8 x (by simpa using hx)

theorem be20_rev (m : Memory) (p : Nat) :
    Spec.fromBE (fun i => m.readLE (p + i) 1) 20 =
      revBytesNat 4 (m.readLE p 4) * 2 ^ 128 + revBytesNat 8 (m.readLE (p + 4) 8) * 2 ^ 64 +
        revBytesNat 8 (m.readLE (p + 12) 8) := by
  have h : ∀ q w, Spec.fromBE (fun i => m.readLE (p + (q + i)) 1) w = revBytesNat w (m.readLE (p + q) w) := by
    intro q w
    rw [revBytes_readLE]
    simp only [Nat.add_assoc]
  have e0 : Spec.fromBE (fun i => m.readLE (p + i) 1) 4 = revBytesNat 4 (m.readLE p 4) :=
    revBytes_readLE m p 4 ▸ rfl
  rw [show 20 = 4 + 16 from rfl, fromBE_add, show 16 = 8 + 8 from rfl, fromBE_add]
  have h2 := h 4 8
  have h3 := h (4 + 8) 8
  simp only [Nat.add_assoc] at h2 h3
  rw [e0, h2, h3]
  simp only [Nat.reduceAdd, Nat.reducePow, Nat.add_mul]
  omega

theorem rc4_val (v : Nat) :
    (BitVec.setWidth 64 (BitVec.ofNat 32
      (revContainersNat 4 1 (BitVec.setWidth 32 (BitVec.ofNat 64 v)).toNat))).toNat = revBytesNat 4 (v % 4294967296) := by
  have hr := revBytes_lt 4 (v % 4294967296)
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, revContainersNat] at *
  have e1 : v % 18446744073709551616 % 4294967296 = v % 4294967296 := by omega
  rw [e1]
  simp only [Nat.mod_mod, Nat.mul_zero, Nat.add_zero]
  omega
theorem rev4_rev4 (x : Nat) (hx : x < 4294967296) : revBytesNat 4 (revBytesNat 4 x) = x :=
  rev_rev 4 x (by simpa using hx)

theorem chunk2n (m : Janus.Arm64.Memory) (a : Nat) :
    (BitVec.setWidth 64 (BitVec.ofNat 32
      (revContainersNat 2 2 (BitVec.setWidth 32 (BitVec.ofNat 64 (m.readLE a 2))).toNat))).toNat % 65536 =
      Spec.fromBE (fun i => m.readLE (a + i) 1) 2 := by
  have := chunk2 m a
  simpa [rot0] using this

end BEsec

theorem byte_val (N y0 y1 y2 y3 : Nat) (hN : N < 32) (h0 : y0 < 18446744073709551616) (h1 : y1 < 18446744073709551616)
    (h2 : y2 < 18446744073709551616) (h3 : y3 < 18446744073709551616) :
    Spec.byte N (y0 + 18446744073709551616 * y1 + 340282366920938463463374607431768211456 * y2 +
        6277101735386680763835789423207666416102355444464034512896 * y3) =
    (if N / 8 = 3 then y0 else if N / 8 = 2 then y1 else if N / 8 = 1 then y2 else y3) / 2 ^ (8 * (7 - N % 8)) % 256 := by
  have hc : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 8 ∨ N = 9 ∨ N = 10 ∨ N = 11 ∨ N = 12 ∨ N = 13 ∨ N = 14 ∨ N = 15 ∨ N = 16 ∨ N = 17 ∨ N = 18 ∨ N = 19 ∨ N = 20 ∨ N = 21 ∨ N = 22 ∨ N = 23 ∨ N = 24 ∨ N = 25 ∨ N = 26 ∨ N = 27 ∨ N = 28 ∨ N = 29 ∨ N = 30 ∨ N = 31 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [Spec.byte, Nat.reduceLT, ite_true, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Nat.reduceEqDiff, ite_false] <;> omega)

theorem pq_eq (t : Nat) (ht : t ≤ 64) : 2 ^ t * 2 ^ (64 - t) = 18446744073709551616 := by
  rw [← Nat.pow_add, show t + (64 - t) = 64 by omega]

theorem shl_lo (x t : Nat) (ht : t ≤ 64) :
    x * 2 ^ t % 18446744073709551616 = 2 ^ t * (x % 2 ^ (64 - t)) := by
  have h := pq_eq t ht
  have hP : 0 < 2 ^ t := Nat.two_pow_pos t
  have hQ : 0 < 2 ^ (64 - t) := Nat.two_pow_pos _
  have hd := Nat.div_add_mod x (2 ^ (64 - t))
  have e1 : x * 2 ^ t = 2 ^ t * (2 ^ (64 - t) * (x / 2 ^ (64 - t))) + 2 ^ t * (x % 2 ^ (64 - t)) := by
    calc x * 2 ^ t = 2 ^ t * x := Nat.mul_comm _ _
      _ = 2 ^ t * (2 ^ (64 - t) * (x / 2 ^ (64 - t)) + x % 2 ^ (64 - t)) := by rw [hd]
      _ = _ := Nat.mul_add _ _ _
  have e2 : 2 ^ t * (2 ^ (64 - t) * (x / 2 ^ (64 - t))) = 18446744073709551616 * (x / 2 ^ (64 - t)) := by
    rw [← Nat.mul_assoc, h]
  have hlt : 2 ^ t * (x % 2 ^ (64 - t)) < 18446744073709551616 := by
    rw [← h]
    exact Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ hQ) hP
  rw [e1, e2, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- `x * 2^t = 2^64 * (x / 2^(64-t)) + (x * 2^t % 2^64)`. -/
theorem shl_split (x t : Nat) (ht : t ≤ 64) :
    x * 2 ^ t = 18446744073709551616 * (x / 2 ^ (64 - t)) + x * 2 ^ t % 18446744073709551616 := by
  have h := pq_eq t ht
  have hQ : 0 < 2 ^ (64 - t) := Nat.two_pow_pos _
  have hd := Nat.div_add_mod x (2 ^ (64 - t))
  have e1 : x * 2 ^ t = 2 ^ t * (2 ^ (64 - t) * (x / 2 ^ (64 - t))) + 2 ^ t * (x % 2 ^ (64 - t)) := by
    calc x * 2 ^ t = 2 ^ t * x := Nat.mul_comm _ _
      _ = 2 ^ t * (2 ^ (64 - t) * (x / 2 ^ (64 - t)) + x % 2 ^ (64 - t)) := by rw [hd]
      _ = _ := Nat.mul_add _ _ _
  have e2 : 2 ^ t * (2 ^ (64 - t) * (x / 2 ^ (64 - t))) = 18446744073709551616 * (x / 2 ^ (64 - t)) := by
    rw [← Nat.mul_assoc, h]
  rw [shl_lo x t ht]
  omega

theorem lo_hi_lt (x y t : Nat) (ht : t < 64) (hy : y < 18446744073709551616) :
    x * 2 ^ t % 18446744073709551616 + y / 2 ^ (64 - t) < 18446744073709551616 := by
  have h := pq_eq t (by omega)
  have hP : 0 < 2 ^ t := Nat.two_pow_pos t
  have hQ : 0 < 2 ^ (64 - t) := Nat.two_pow_pos _
  rw [shl_lo x t (by omega)]
  have h1 : y / 2 ^ (64 - t) < 2 ^ t := by
    rw [Nat.div_lt_iff_lt_mul hQ]
    rw [h]; exact hy
  have h2 : x % 2 ^ (64 - t) + 1 ≤ 2 ^ (64 - t) := Nat.mod_lt _ hQ
  have h3 : 2 ^ t * (x % 2 ^ (64 - t) + 1) ≤ 2 ^ t * 2 ^ (64 - t) := Nat.mul_le_mul_left _ h2
  rw [Nat.mul_add, h] at h3
  omega

theorem lsh_expand (x0 x1 x2 x3 e : Nat) :
    (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 +
        6277101735386680763835789423207666416102355444464034512896 * x3) * e =
      x0 * e + 18446744073709551616 * (x1 * e) + 340282366920938463463374607431768211456 * (x2 * e) +
        6277101735386680763835789423207666416102355444464034512896 * (x3 * e) := by
  simp only [Nat.add_mul, Nat.mul_assoc]

theorem lsh0_t (x0 x1 x2 x3 t : Nat) (ht : t < 64) (h0 : x0 < 18446744073709551616) (h1 : x1 < 18446744073709551616)
    (h2 : x2 < 18446744073709551616) (h3 : x3 < 18446744073709551616) :
    x0 * 2 ^ t % 18446744073709551616 + 18446744073709551616 * (x1 * 2 ^ t % 18446744073709551616 + x0 / 2 ^ (64 - t)) +
      340282366920938463463374607431768211456 * (x2 * 2 ^ t % 18446744073709551616 + x1 / 2 ^ (64 - t)) +
      6277101735386680763835789423207666416102355444464034512896 * (x3 * 2 ^ t % 18446744073709551616 + x2 / 2 ^ (64 - t)) =
    (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 +
        6277101735386680763835789423207666416102355444464034512896 * x3) * 2 ^ t %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  have s0 := shl_split x0 t (by omega)
  have s1 := shl_split x1 t (by omega)
  have s2 := shl_split x2 t (by omega)
  have s3 := shl_split x3 t (by omega)
  have l1 := lo_hi_lt x1 x0 t ht h0
  have l2 := lo_hi_lt x2 x1 t ht h1
  have l3 := lo_hi_lt x3 x2 t ht h2
  have l0 : x0 * 2 ^ t % 18446744073709551616 < 18446744073709551616 := Nat.mod_lt _ (by decide)
  rw [lsh_expand]
  omega

theorem pow_shift (X t k : Nat) : X * 2 ^ (64 * k + t) = 2 ^ (64 * k) * (X * 2 ^ t) := by
  rw [Nat.pow_add]; ac_rfl

theorem lsh1_t (x0 x1 x2 x3 t : Nat) (ht : t < 64) (h0 : x0 < 18446744073709551616) (h1 : x1 < 18446744073709551616)
    (h2 : x2 < 18446744073709551616) (h3 : x3 < 18446744073709551616) :
    18446744073709551616 * (x0 * 2 ^ t % 18446744073709551616) +
      340282366920938463463374607431768211456 * (x1 * 2 ^ t % 18446744073709551616 + x0 / 2 ^ (64 - t)) +
      6277101735386680763835789423207666416102355444464034512896 * (x2 * 2 ^ t % 18446744073709551616 + x1 / 2 ^ (64 - t)) =
    (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 + 6277101735386680763835789423207666416102355444464034512896 * x3) * 2 ^ (64 + t) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  have s0 := shl_split x0 t (by omega)
  have s1 := shl_split x1 t (by omega)
  have s2 := shl_split x2 t (by omega)
  have s3 := shl_split x3 t (by omega)
  have l1 := lo_hi_lt x1 x0 t ht h0
  have l2 := lo_hi_lt x2 x1 t ht h1
  have e := pow_shift (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 + 6277101735386680763835789423207666416102355444464034512896 * x3) t 1
  simp only [Nat.mul_one] at e
  rw [e, lsh_expand]
  have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  rw [this]
  omega

theorem lsh2_t (x0 x1 x2 x3 t : Nat) (ht : t < 64) (h0 : x0 < 18446744073709551616) (h1 : x1 < 18446744073709551616)
    (h2 : x2 < 18446744073709551616) (h3 : x3 < 18446744073709551616) :
    340282366920938463463374607431768211456 * (x0 * 2 ^ t % 18446744073709551616) +
      6277101735386680763835789423207666416102355444464034512896 * (x1 * 2 ^ t % 18446744073709551616 + x0 / 2 ^ (64 - t)) =
    (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 + 6277101735386680763835789423207666416102355444464034512896 * x3) * 2 ^ (128 + t) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  have s0 := shl_split x0 t (by omega)
  have s1 := shl_split x1 t (by omega)
  have s2 := shl_split x2 t (by omega)
  have s3 := shl_split x3 t (by omega)
  have l1 := lo_hi_lt x1 x0 t ht h0
  have e := pow_shift (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 + 6277101735386680763835789423207666416102355444464034512896 * x3) t 2
  simp only [show 64 * 2 = 128 from rfl] at e
  rw [e, lsh_expand]
  have : (2 : Nat) ^ 128 = 340282366920938463463374607431768211456 := by decide
  rw [this]
  omega

theorem lsh3_t (x0 x1 x2 x3 t : Nat) (ht : t < 64) (h0 : x0 < 18446744073709551616) (h1 : x1 < 18446744073709551616)
    (h2 : x2 < 18446744073709551616) (h3 : x3 < 18446744073709551616) :
    6277101735386680763835789423207666416102355444464034512896 * (x0 * 2 ^ t % 18446744073709551616) =
    (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 + 6277101735386680763835789423207666416102355444464034512896 * x3) * 2 ^ (192 + t) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  have s0 := shl_split x0 t (by omega)
  have s1 := shl_split x1 t (by omega)
  have s2 := shl_split x2 t (by omega)
  have s3 := shl_split x3 t (by omega)
  have e := pow_shift (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 + 6277101735386680763835789423207666416102355444464034512896 * x3) t 3
  simp only [show 64 * 3 = 192 from rfl] at e
  rw [e, lsh_expand]
  have : (2 : Nat) ^ 192 = 6277101735386680763835789423207666416102355444464034512896 := by decide
  rw [this]
  omega

theorem shl_or (a b t : Nat) (ht : t < 64) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    (a * 2 ^ t % 18446744073709551616 ||| b / 2 ^ (64 - t)) % 18446744073709551616 =
      a * 2 ^ t % 18446744073709551616 + b / 2 ^ (64 - t) := by
  have h := pq_eq t (by omega)
  have hQ : 0 < 2 ^ (64 - t) := Nat.two_pow_pos _
  have hv : b / 2 ^ (64 - t) < 2 ^ t := by
    rw [Nat.div_lt_iff_lt_mul hQ, h]; exact hb
  have hlt := lo_hi_lt a b t ht hb
  rw [shl_lo a t (by omega)]
  rw [Nat.or_comm, show 2 ^ t * (a % 2 ^ (64 - t)) = (a % 2 ^ (64 - t)) * 2 ^ t from Nat.mul_comm _ _, or_hi _ _ _ hv]
  rw [shl_lo a t (by omega)] at hlt
  rw [Nat.mod_eq_of_lt (by rw [Nat.mul_comm] at hlt; omega)]
  rw [Nat.mul_comm]; omega

theorem shl_or_bv (a b t : Nat) (ht : t < 64) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    (a * 2 ^ t % 18446744073709551616 ||| (if 64 - t < 64 then BitVec.ofNat 64 b >>> ((64 - t) % 64) else 0#64).toNat) %
      18446744073709551616 = a * 2 ^ t % 18446744073709551616 + b / 2 ^ (64 - t) := by
  by_cases h0 : t = 0
  · subst h0
    simp only [Nat.sub_zero, show ¬ (64 < 64) from by decide, if_false]
    have : b / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by simpa using hb)
    simp [this]
  · have hc : 64 - t < 64 := by omega
    simp only [hc, if_true, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega : 64 - t < 64)] 
    exact shl_or a b t ht ha hb


theorem shl_or_bv0 (a b t : Nat) (ht : 1 ≤ t) (ht2 : t < 64) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    (a * 2 ^ t % 18446744073709551616 ||| b / 2 ^ ((64 - t) % 64)) % 18446744073709551616 =
      a * 2 ^ t % 18446744073709551616 + b / 2 ^ (64 - t) := by
  rw [Nat.mod_eq_of_lt (by omega : 64 - t < 64)]
  exact shl_or a b t ht2 ha hb

theorem lsh_big (X m : Nat) (hm : 256 ≤ m) : X * 2 ^ m % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0 := by
  have : 2 ^ m = 2 ^ (m - 256) * 2 ^ 256 := by rw [← Nat.pow_add]; congr 1; omega
  rw [this, ← Nat.mul_assoc]
  exact Nat.mul_mod_left _ _

theorem shr_hi (x t : Nat) (ht : t < 64) : x * 2 ^ (64 - t) % 18446744073709551616 = 2 ^ (64 - t) * (x % 2 ^ t) := by
  have := shl_lo x (64 - t) (by omega)
  rw [show 64 - (64 - t) = t by omega] at this
  exact this

theorem rsh0_t (x0 x1 x2 x3 t : Nat) (ht : t < 64) (h0 : x0 < 18446744073709551616) (h1 : x1 < 18446744073709551616)
    (h2 : x2 < 18446744073709551616) (h3 : x3 < 18446744073709551616) :
    (x0 / 2 ^ t + x1 * 2 ^ (64 - t) % 18446744073709551616) +
      18446744073709551616 * (x1 / 2 ^ t + x2 * 2 ^ (64 - t) % 18446744073709551616) +
      340282366920938463463374607431768211456 * (x2 / 2 ^ t + x3 * 2 ^ (64 - t) % 18446744073709551616) +
      6277101735386680763835789423207666416102355444464034512896 * (x3 / 2 ^ t) =
    (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 +
        6277101735386680763835789423207666416102355444464034512896 * x3) / 2 ^ t := by
  have hP : 0 < 2 ^ t := Nat.two_pow_pos t
  have hpq := pq_eq t (by omega)
  have d0 := Nat.div_add_mod x0 (2 ^ t)
  have d1 := Nat.div_add_mod x1 (2 ^ t)
  have d2 := Nat.div_add_mod x2 (2 ^ t)
  have d3 := Nat.div_add_mod x3 (2 ^ t)
  have rl0 := Nat.mod_lt x0 hP
  have rl1 := Nat.mod_lt x1 hP
  have rl2 := Nat.mod_lt x2 hP
  have rl3 := Nat.mod_lt x3 hP
  rw [shr_hi x1 t ht, shr_hi x2 t ht, shr_hi x3 t ht]
  -- let P, Q, y_i, r_i
  generalize hPdef : 2 ^ t = P at *
  generalize hQdef : 2 ^ (64 - t) = Q at *
  generalize x0 / P = y0 at *
  generalize x1 / P = y1 at *
  generalize x2 / P = y2 at *
  generalize x3 / P = y3 at *
  generalize x0 % P = r0 at *
  generalize x1 % P = r1 at *
  generalize x2 % P = r2 at *
  generalize x3 % P = r3 at *
  have k : ∀ r : Nat, Q * (P * r) = 18446744073709551616 * r := by
    intro r; rw [← Nat.mul_assoc, Nat.mul_comm Q P, hpq]
  have e : P * ((y0 + Q * r1) + 18446744073709551616 * (y1 + Q * r2) + 340282366920938463463374607431768211456 * (y2 + Q * r3) + 6277101735386680763835789423207666416102355444464034512896 * y3) =
      P * y0 + Q * (P * r1) + 18446744073709551616 * (P * y1) + 18446744073709551616 * (Q * (P * r2)) + 340282366920938463463374607431768211456 * (P * y2) + 340282366920938463463374607431768211456 * (Q * (P * r3)) + 6277101735386680763835789423207666416102355444464034512896 * (P * y3) := by
    simp only [Nat.mul_add, Nat.mul_left_comm P, Nat.mul_assoc]
    omega
  rw [k r1, k r2, k r3] at e
  generalize (y0 + Q * r1 + 18446744073709551616 * (y1 + Q * r2) + 340282366920938463463374607431768211456 * (y2 + Q * r3) + 6277101735386680763835789423207666416102355444464034512896 * y3) = R at e ⊢
  have hc := Nat.mul_comm R P
  symm
  apply Nat.div_eq_of_lt_le
  · omega
  · rw [Nat.add_mul, Nat.one_mul]; omega

theorem div_shift (X k t : Nat) : X / 2 ^ (64 * k + t) = X / 2 ^ (64 * k) / 2 ^ t := by
  rw [Nat.pow_add, Nat.div_div_eq_div_mul]

theorem rsh1_t (x0 x1 x2 x3 t : Nat) (ht : t < 64) (h0 : x0 < 18446744073709551616) (h1 : x1 < 18446744073709551616)
    (h2 : x2 < 18446744073709551616) (h3 : x3 < 18446744073709551616) :
    (x1 / 2 ^ t + x2 * 2 ^ (64 - t) % 18446744073709551616) + 18446744073709551616 * (x2 / 2 ^ t + x3 * 2 ^ (64 - t) % 18446744073709551616) +
      340282366920938463463374607431768211456 * (x3 / 2 ^ t) = (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 + 6277101735386680763835789423207666416102355444464034512896 * x3) / 2 ^ (64 + t) := by
  have e := div_shift (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 + 6277101735386680763835789423207666416102355444464034512896 * x3) 1 t
  simp only [Nat.mul_one] at e
  have e1 : (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 + 6277101735386680763835789423207666416102355444464034512896 * x3) / 2 ^ 64 = x1 + 18446744073709551616 * x2 + 340282366920938463463374607431768211456 * x3 := by
    have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
    rw [this]; omega
  rw [e, e1]
  have := rsh0_t x1 x2 x3 0 t ht h1 h2 h3 (by decide)
  simp only [Nat.zero_mul, Nat.zero_mod, Nat.zero_div, Nat.add_zero, Nat.mul_zero] at this
  exact this

theorem rsh2_t (x0 x1 x2 x3 t : Nat) (ht : t < 64) (h0 : x0 < 18446744073709551616) (h1 : x1 < 18446744073709551616)
    (h2 : x2 < 18446744073709551616) (h3 : x3 < 18446744073709551616) :
    (x2 / 2 ^ t + x3 * 2 ^ (64 - t) % 18446744073709551616) + 18446744073709551616 * (x3 / 2 ^ t) = (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 + 6277101735386680763835789423207666416102355444464034512896 * x3) / 2 ^ (128 + t) := by
  have e := div_shift (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 + 6277101735386680763835789423207666416102355444464034512896 * x3) 2 t
  simp only [show 64 * 2 = 128 from rfl] at e
  have e1 : (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 + 6277101735386680763835789423207666416102355444464034512896 * x3) / 2 ^ 128 = x2 + 18446744073709551616 * x3 := by
    have : (2 : Nat) ^ 128 = 340282366920938463463374607431768211456 := by decide
    rw [this]; omega
  rw [e, e1]
  have := rsh0_t x2 x3 0 0 t ht h2 h3 (by decide) (by decide)
  simp only [Nat.zero_mul, Nat.zero_mod, Nat.zero_div, Nat.add_zero, Nat.mul_zero] at this
  exact this

theorem rsh3_t (x0 x1 x2 x3 t : Nat) (ht : t < 64) (h0 : x0 < 18446744073709551616) (h1 : x1 < 18446744073709551616)
    (h2 : x2 < 18446744073709551616) (h3 : x3 < 18446744073709551616) :
    x3 / 2 ^ t = (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 + 6277101735386680763835789423207666416102355444464034512896 * x3) / 2 ^ (192 + t) := by
  have e := div_shift (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 + 6277101735386680763835789423207666416102355444464034512896 * x3) 3 t
  simp only [show 64 * 3 = 192 from rfl] at e
  have e1 : (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 + 6277101735386680763835789423207666416102355444464034512896 * x3) / 2 ^ 192 = x3 := by
    have : (2 : Nat) ^ 192 = 6277101735386680763835789423207666416102355444464034512896 := by decide
    rw [this]; omega
  rw [e, e1]

theorem rsh_big (X m : Nat) (hX : X < 115792089237316195423570985008687907853269984665640564039457584007913129639936) (hm : 256 ≤ m) : X / 2 ^ m = 0 := by
  apply Nat.div_eq_of_lt
  calc X < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := hX
    _ = 2 ^ 256 := by decide
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm

theorem shr_or_nat (a b t : Nat) (ht1 : 1 ≤ t) (ht : t < 64) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    (a * 2 ^ ((64 - t) % 64) % 18446744073709551616 ||| b / 2 ^ t) % 18446744073709551616 =
      b / 2 ^ t + a * 2 ^ (64 - t) % 18446744073709551616 := by
  have h := pq_eq t (by omega)
  have hP : 0 < 2 ^ t := Nat.two_pow_pos t
  have hS : 0 < 2 ^ (64 - t) := Nat.two_pow_pos _
  rw [Nat.mod_eq_of_lt (by omega : 64 - t < 64), shr_hi a t ht]
  have hv : b / 2 ^ t < 2 ^ (64 - t) := by
    rw [Nat.div_lt_iff_lt_mul hP, Nat.mul_comm, h]; exact hb
  have hc : a % 2 ^ t + 1 ≤ 2 ^ t := Nat.mod_lt _ hP
  have h3 : 2 ^ (64 - t) * (a % 2 ^ t + 1) ≤ 2 ^ (64 - t) * 2 ^ t := Nat.mul_le_mul_left _ hc
  rw [Nat.mul_add, Nat.mul_comm (2 ^ (64 - t)) (2 ^ t), h] at h3
  rw [Nat.or_comm, show 2 ^ (64 - t) * (a % 2 ^ t) = (a % 2 ^ t) * 2 ^ (64 - t) from Nat.mul_comm _ _, or_hi _ _ _ hv]
  rw [Nat.mod_eq_of_lt (by rw [Nat.mul_comm (a % 2 ^ t)] at *; omega)]

theorem shr_or_bv (a b t : Nat) (ht : t < 64) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    ((if 64 - t < 64 then BitVec.ofNat 64 (a * 2 ^ ((64 - t) % 64)) else 0#64).toNat ||| b / 2 ^ t) % 18446744073709551616 =
      b / 2 ^ t + a * 2 ^ (64 - t) % 18446744073709551616 := by
  by_cases h0 : t = 0
  · subst h0
    simp only [Nat.sub_zero, show ¬ (64 < 64) from by decide, if_false]
    have : a * 2 ^ 64 % 18446744073709551616 = 0 := by
      show a * 18446744073709551616 % 18446744073709551616 = 0
      exact Nat.mul_mod_left _ _
    simp only [this, Nat.pow_zero, Nat.div_one]
    simp [Nat.mod_eq_of_lt hb]
  · have hc : 64 - t < 64 := by omega
    simp only [hc, if_true, BitVec.toNat_ofNat, Nat.reducePow]
    have hlt : a * 2 ^ ((64 - t) % 64) < 18446744073709551616 ∨ True := Or.inr trivial
    rw [Nat.mod_eq_of_lt (by omega : 64 - t < 64)]
    have := shr_or_nat a b t (by omega) ht ha hb
    rw [Nat.mod_eq_of_lt (by omega : 64 - t < 64)] at this
    exact this

theorem rd16 (m : Janus.Arm64.Memory) (a : Nat) :
    m.readLE a 16 = m.readLE a 8 + 18446744073709551616 * m.readLE (a + 8) 8 := by
  rw [show 16 = 8 + 8 from rfl, Janus.Arm64.Memory.readLE_add]

section W16sec
open Janus.Arm64

theorem w16_lo (m : Memory) (a v : Nat) : (m.writeLE a 16 v).readLE a 8 = v % 18446744073709551616 := by
  have := Memory.readLE_writeLE_inside (m := m) (a := a) (n := 16) (b := a) (k := 8) v (Nat.le_refl _) (by omega)
  rw [this]; simp

theorem w16_hi (m : Memory) (a v : Nat) : (m.writeLE a 16 v).readLE (a + 8) 8 = v / 18446744073709551616 % 18446744073709551616 := by
  have := Memory.readLE_writeLE_inside (m := m) (a := a) (n := 16) (b := a + 8) (k := 8) v (by omega) (by omega)
  rw [this]; simp

end W16sec

theorem readLE_writeLE_eq (m : Janus.Arm64.Memory) {a b n : Nat} (v : Nat) (h : b = a) :
    (m.writeLE a n v).readLE b n = v % 256 ^ n := by
  subst h; exact Janus.Arm64.Memory.readLE_writeLE_self m b n v

theorem lo16 (A B : Nat) (hA : A < 18446744073709551616) : (A + 18446744073709551616 * B) % 18446744073709551616 = A := by
  omega

theorem hi16 (A B : Nat) (hA : A < 18446744073709551616) (hB : B < 18446744073709551616) :
    (A + 18446744073709551616 * B) / 18446744073709551616 % 18446744073709551616 = B := by
  omega

theorem bv128_zero_toNat : BitVec.toNat (OfNat.ofNat 0 : BitVec 128) = 0 := rfl

theorem rot3_idx (b : Nat) (hb : b < 18446744073709551616) :
    (b / 8 ||| b * 2305843009213693952 % 18446744073709551616) % 18446744073709551616 % 2305843009213693952 = b / 8 := by
  have e : b * 2305843009213693952 % 18446744073709551616 = (b % 8) * 2305843009213693952 := by omega
  have h1 : b / 8 < 2305843009213693952 := by omega
  rw [e, show (b % 8) * 2305843009213693952 = (b % 8) * 2 ^ 61 from rfl, or_hi _ _ 61 (by simpa using h1)]
  omega
theorem shrd_val (x y t : Nat) (ht : t < 64) (hx : x < 18446744073709551616) :
    (y * 18446744073709551616 + x) / 2 ^ t % 18446744073709551616 =
      x / 2 ^ t + y * 2 ^ (64 - t) % 18446744073709551616 := by
  have h := pq_eq t (by omega)
  have hP : 0 < 2 ^ t := Nat.two_pow_pos t
  have hQ : 0 < 2 ^ (64 - t) := Nat.two_pow_pos _
  have e1 : (y * 18446744073709551616 + x) / 2 ^ t = y * 2 ^ (64 - t) + x / 2 ^ t := by
    rw [← h, Nat.mul_comm (2 ^ t), ← Nat.mul_assoc]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP]
    omega
  have hv : x / 2 ^ t < 2 ^ (64 - t) := by
    rw [Nat.div_lt_iff_lt_mul hP, Nat.mul_comm, h]; exact hx
  have hA := shr_hi y t ht
  have hc : y % 2 ^ t + 1 ≤ 2 ^ t := Nat.mod_lt _ hP
  have h3 : 2 ^ (64 - t) * (y % 2 ^ t + 1) ≤ 2 ^ (64 - t) * 2 ^ t := Nat.mul_le_mul_left _ hc
  rw [Nat.mul_add, Nat.mul_comm (2 ^ (64 - t)) (2 ^ t), h, Nat.mul_one] at h3
  rw [e1]
  generalize x / 2 ^ t = h' at *
  generalize y * 2 ^ (64 - t) = A at *
  generalize 2 ^ (64 - t) * (y % 2 ^ t) = B at *
  generalize 2 ^ (64 - t) = Q at *
  omega

theorem shld_val (x y t : Nat) (ht : t < 64) (hx : x < 18446744073709551616) (hy : y < 18446744073709551616) :
    (y * 18446744073709551616 + x) * 2 ^ t / 18446744073709551616 % 18446744073709551616 =
      y * 2 ^ t % 18446744073709551616 + x / 2 ^ (64 - t) := by
  have s := shl_split x t (by omega)
  have l := lo_hi_lt y x t ht hx
  have e : (y * 18446744073709551616 + x) * 2 ^ t = 18446744073709551616 * (y * 2 ^ t) + x * 2 ^ t := by
    rw [Nat.add_mul, Nat.mul_comm y 18446744073709551616, Nat.mul_assoc]
  rw [e]
  generalize y * 2 ^ t = YP at *
  generalize x * 2 ^ t = XP at *
  generalize x / 2 ^ (64 - t) = h at *
  omega

theorem shr_or_nat0 (a b t : Nat) (ht1 : 1 ≤ t) (ht : t < 64) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    (a * 2 ^ (64 - t) % 18446744073709551616 ||| b / 2 ^ t) =
      b / 2 ^ t + a * 2 ^ (64 - t) % 18446744073709551616 := by
  have h := shr_or_nat a b t ht1 ht ha hb
  rw [Nat.mod_eq_of_lt (by omega : 64 - t < 64)] at h
  have hlt : (a * 2 ^ (64 - t) % 18446744073709551616 ||| b / 2 ^ t) < 18446744073709551616 :=
    Nat.or_lt_two_pow (n := 64) (Nat.mod_lt _ (by decide)) (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hb)
  rwa [Nat.mod_eq_of_lt hlt] at h

theorem and_ones_lt (a : Nat) (h : a < 18446744073709551616) : a &&& 18446744073709551615 = a :=
  Nat.and_two_pow_sub_one_of_lt_two_pow (n := 64) h
theorem ones_and_lt (a : Nat) (h : a < 18446744073709551616) : 18446744073709551615 &&& a = a := by
  rw [Nat.and_comm]; exact and_ones_lt a h

theorem shl_or_nat0 (a b t : Nat) (ht1 : 1 ≤ t) (ht : t < 64) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    (a * 2 ^ t % 18446744073709551616 ||| b / 2 ^ (64 - t)) =
      a * 2 ^ t % 18446744073709551616 + b / 2 ^ (64 - t) := by
  have h := shl_or a b t ht ha hb
  have hlt : (a * 2 ^ t % 18446744073709551616 ||| b / 2 ^ (64 - t)) < 18446744073709551616 :=
    Nat.or_lt_two_pow (n := 64) (Nat.mod_lt _ (by decide)) (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hb)
  rwa [Nat.mod_eq_of_lt hlt] at h

theorem shl_or_nat0' (a b t : Nat) (ht1 : 1 ≤ t) (ht : t < 64) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    (b / 2 ^ (64 - t) ||| a * 2 ^ t % 18446744073709551616) =
      a * 2 ^ t % 18446744073709551616 + b / 2 ^ (64 - t) := by
  rw [Nat.or_comm]; exact shl_or_nat0 a b t ht1 ht ha hb

@[simp] theorem rd4mod (m : Janus.Arm64.Memory) (a : Nat) : m.readLE a 4 % 4294967296 = m.readLE a 4 := by
  exact Nat.mod_eq_of_lt (by simpa using Janus.Arm64.Memory.readLE_lt m a 4)
@[simp] theorem rd2mod (m : Janus.Arm64.Memory) (a : Nat) : m.readLE a 2 % 65536 = m.readLE a 2 := by
  exact Nat.mod_eq_of_lt (by simpa using Janus.Arm64.Memory.readLE_lt m a 2)
@[simp] theorem rd1mod (m : Janus.Arm64.Memory) (a : Nat) : m.readLE a 1 % 256 = m.readLE a 1 := by
  exact Nat.mod_eq_of_lt (by simpa using Janus.Arm64.Memory.readLE_lt m a 1)

theorem or_hi_comm (a c k : Nat) (ha : a < 2 ^ k) : c * 2 ^ k ||| a = a + c * 2 ^ k := by
  rw [Nat.or_comm]; exact or_hi a c k ha
theorem orc_hi16 (a c : Nat) (ha : a < 65536) : c * 65536 ||| a = a + c * 65536 := or_hi_comm a c 16 ha
theorem orc_hi24 (a c : Nat) (ha : a < 16777216) : c * 16777216 ||| a = a + c * 16777216 := or_hi_comm a c 24 ha
theorem orc_hi32 (a c : Nat) (ha : a < 4294967296) : c * 4294967296 ||| a = a + c * 4294967296 := or_hi_comm a c 32 ha
theorem orc_hi40 (a c : Nat) (ha : a < 1099511627776) : c * 1099511627776 ||| a = a + c * 1099511627776 := or_hi_comm a c 40 ha
theorem orc_hi48 (a c : Nat) (ha : a < 281474976710656) : c * 281474976710656 ||| a = a + c * 281474976710656 := or_hi_comm a c 48 ha
theorem orc_hi56 (a c : Nat) (ha : a < 72057594037927936) : c * 72057594037927936 ||| a = a + c * 72057594037927936 := or_hi_comm a c 56 ha

theorem sb_val4 (m : Janus.Arm64.Memory) (p z : Nat) :
    Janus.Arm64.revBytesNat 4 (m.readLE p 4 % 4294967296) % 4294967296 +
        340282366920938463463374607431768211456 *
          (BitVec.toNat (OfNat.ofNat 0 : BitVec 128) / 256 ^ (z - z) % 18446744073709551616) +
      6277101735386680763835789423207666416102355444464034512896 *
        (BitVec.toNat (OfNat.ofNat 0 : BitVec 128) / 18446744073709551616) =
    Spec.fromBE (fun i => m.readLE (p + i) 1) 4 := by
  have h1 : BitVec.toNat (OfNat.ofNat 0 : BitVec 128) / 256 ^ (z - z) % 18446744073709551616 = 0 := by
    simp [bv128_zero_toNat]
  have h2 : BitVec.toNat (OfNat.ofNat 0 : BitVec 128) / 18446744073709551616 = 0 := by
    simp [bv128_zero_toNat]
  have h3 : Janus.Arm64.revBytesNat 4 (m.readLE p 4 % 4294967296) = Spec.fromBE (fun i => m.readLE (p + i) 1) 4 := by
    rw [rd4mod]; exact revBytes_readLE m p 4
  have h4 : Spec.fromBE (fun i => m.readLE (p + i) 1) 4 < 4294967296 := by
    simp only [Spec.fromBE, Nat.add_zero, Nat.reducePow, Nat.reduceAdd, Nat.zero_add]
    have := rd1_lt m p; have := rd1_lt m (p + 1); have := rd1_lt m (p + 2); have := rd1_lt m (p + 3)
    omega
  have h5 := Nat.mod_eq_of_lt h4
  omega
theorem sb_val8 (m : Janus.Arm64.Memory) (p z : Nat) :
    Janus.Arm64.revBytesNat 8 (m.readLE p 8) % 18446744073709551616 +
        340282366920938463463374607431768211456 *
          (BitVec.toNat (OfNat.ofNat 0 : BitVec 128) / 256 ^ (z - z) % 18446744073709551616) +
      6277101735386680763835789423207666416102355444464034512896 *
        (BitVec.toNat (OfNat.ofNat 0 : BitVec 128) / 18446744073709551616) =
    Spec.fromBE (fun i => m.readLE (p + i) 1) 8 := by
  have h1 : BitVec.toNat (OfNat.ofNat 0 : BitVec 128) / 256 ^ (z - z) % 18446744073709551616 = 0 := by
    simp [bv128_zero_toNat]
  have h2 : BitVec.toNat (OfNat.ofNat 0 : BitVec 128) / 18446744073709551616 = 0 := by
    simp [bv128_zero_toNat]
  have h3 : Janus.Arm64.revBytesNat 8 (m.readLE p 8) = Spec.fromBE (fun i => m.readLE (p + i) 1) 8 :=
    revBytes_readLE m p 8
  have h4 := revBytes_lt 8 (m.readLE p 8)
  simp only [Nat.reducePow] at h4
  omega

theorem sb_val12 (m : Janus.Arm64.Memory) (p z : Nat) :
    Janus.Arm64.revBytesNat 8 (m.readLE (p + 4) 8) % 18446744073709551616 +
          18446744073709551616 * (Janus.Arm64.revBytesNat 4 (m.readLE p 4 % 4294967296) % 4294967296) +
        340282366920938463463374607431768211456 *
          (BitVec.toNat (OfNat.ofNat 0 : BitVec 128) / 256 ^ (z - z) % 18446744073709551616) +
      6277101735386680763835789423207666416102355444464034512896 *
        (BitVec.toNat (OfNat.ofNat 0 : BitVec 128) / 18446744073709551616) =
    Spec.fromBE (fun i => m.readLE (p + i) 1) 12 := by
  have h1 : BitVec.toNat (OfNat.ofNat 0 : BitVec 128) / 256 ^ (z - z) % 18446744073709551616 = 0 := by
    simp [bv128_zero_toNat]
  have h2 : BitVec.toNat (OfNat.ofNat 0 : BitVec 128) / 18446744073709551616 = 0 := by
    simp [bv128_zero_toNat]
  have e : Spec.fromBE (fun i => m.readLE (p + i) 1) 12 =
      Spec.fromBE (fun i => m.readLE (p + i) 1) 4 * 256 ^ 8 + Spec.fromBE (fun i => m.readLE (p + (4 + i)) 1) 8 :=
    fromBE_add _ 4 8
  have h3 : Janus.Arm64.revBytesNat 4 (m.readLE p 4 % 4294967296) = Spec.fromBE (fun i => m.readLE (p + i) 1) 4 := by
    rw [rd4mod]; exact revBytes_readLE m p 4
  have h3' : Janus.Arm64.revBytesNat 8 (m.readLE (p + 4) 8) = Spec.fromBE (fun i => m.readLE (p + (4 + i)) 1) 8 := by
    rw [revBytes_readLE]; simp only [Nat.add_assoc]
  have h4 := revBytes_lt 4 (m.readLE p 4 % 4294967296)
  have h4' := revBytes_lt 8 (m.readLE (p + 4) 8)
  simp only [Nat.reducePow] at h4 h4' e
  omega

theorem sb_val16 (m : Janus.Arm64.Memory) (p z : Nat) :
    Janus.Arm64.revBytesNat 8 (m.readLE (p + 8) 8) % 18446744073709551616 +
          18446744073709551616 * (Janus.Arm64.revBytesNat 8 (m.readLE p 8) % 18446744073709551616) +
        340282366920938463463374607431768211456 *
          (BitVec.toNat (OfNat.ofNat 0 : BitVec 128) / 256 ^ (z - z) % 18446744073709551616) +
      6277101735386680763835789423207666416102355444464034512896 *
        (BitVec.toNat (OfNat.ofNat 0 : BitVec 128) / 18446744073709551616) =
    Spec.fromBE (fun i => m.readLE (p + i) 1) 16 := by
  have h1 : BitVec.toNat (OfNat.ofNat 0 : BitVec 128) / 256 ^ (z - z) % 18446744073709551616 = 0 := by
    simp [bv128_zero_toNat]
  have h2 : BitVec.toNat (OfNat.ofNat 0 : BitVec 128) / 18446744073709551616 = 0 := by
    simp [bv128_zero_toNat]
  have e : Spec.fromBE (fun i => m.readLE (p + i) 1) 16 =
      Spec.fromBE (fun i => m.readLE (p + i) 1) 8 * 256 ^ 8 + Spec.fromBE (fun i => m.readLE (p + (8 + i)) 1) 8 :=
    fromBE_add _ 8 8
  have h3 : Janus.Arm64.revBytesNat 8 (m.readLE p 8) = Spec.fromBE (fun i => m.readLE (p + i) 1) 8 :=
    revBytes_readLE m p 8
  have h3' : Janus.Arm64.revBytesNat 8 (m.readLE (p + 8) 8) = Spec.fromBE (fun i => m.readLE (p + (8 + i)) 1) 8 := by
    rw [revBytes_readLE]; simp only [Nat.add_assoc]
  have h4 := revBytes_lt 8 (m.readLE p 8)
  have h4' := revBytes_lt 8 (m.readLE (p + 8) 8)
  simp only [Nat.reducePow] at h4 h4' e
  omega

theorem bswap16 (v : Nat) (hv : v < 65536) :
    ((BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v))) &&& 18446744073709486080#64 |||
      BitVec.setWidth 64 ((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v)))).rotateLeft 8)).toNat
      = v % 256 * 256 + v / 256 := by
  simp [BitVec.toNat_or, BitVec.toNat_and, BitVec.rotateLeft, BitVec.rotateLeftAux]
  have h0 : v % 65536 = v := Nat.mod_eq_of_lt hv
  have h1 : v % 65536 % 18446744073709551616 = v := by omega
  rw [h1, h0]
  have hand : v &&& 18446744073709486080 = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    have hm : (18446744073709486080 : Nat) = 2 ^ 16 * 281474976710655 + 0 := by decide
    by_cases hi : i < 16
    · rw [hm, Nat.testBit_two_pow_mul_add _ (by decide : (0:Nat) < 2 ^ 16)]
      simp [hi]
    · have : v.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by simpa using hv : v < 2 ^ 16) (Nat.pow_le_pow_right (by decide : 2 > 0) (by omega : 16 ≤ i)))
      simp [this]
  rw [hand, Nat.zero_or]
  have e1 : v <<< 8 % 65536 = v % 256 * 256 := by
    simp only [Nat.shiftLeft_eq]; omega
  have e2 : v >>> 8 = v / 256 := by rw [Nat.shiftRight_eq_div_pow]
  rw [e1, e2, Nat.or_comm]
  have e3 : v % 256 * 256 % 18446744073709551616 = v % 256 * 256 := by omega
  rw [e3]
  have := or_hi (v / 256) (v % 256) 8 (by omega)
  simp only [Nat.reducePow] at this
  omega
theorem rd2_lt (m : Janus.Arm64.Memory) (a : Nat) : m.readLE a 2 < 65536 := by
  simpa using Janus.Arm64.Memory.readLE_lt m a 2

theorem rd2_bytes (m : Janus.Arm64.Memory) (a : Nat) : m.readLE a 2 = m.readLE a 1 + 256 * m.readLE (a + 1) 1 := by
  rw [show 2 = 1 + 1 from rfl, Janus.Arm64.Memory.readLE_add]

theorem bswap16n (v : Nat) (hv : v < 65536) :
    (((BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v))) &&& 18446744073709486080#64).toNat |||
      (BitVec.setWidth 64 ((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v)))).rotateLeft 8)).toNat)
      = v % 256 * 256 + v / 256 := by
  have := bswap16 v hv
  rwa [BitVec.toNat_or] at this

theorem bswap16m (v : Nat) (hv : v < 65536) :
    (((BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v))) &&& 18446744073709486080#64).toNat |||
      ((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v)))).rotateLeft 8).toNat)
      = v % 256 * 256 + v / 256 := by
  have := bswap16n v hv
  have h : (BitVec.setWidth 64 ((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v)))).rotateLeft 8)).toNat =
      ((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v)))).rotateLeft 8).toNat := by
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))
  rwa [h] at this

theorem bswap16w (v : Nat) (hv : v < 65536) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 16
      ((BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v))) &&& 18446744073709486080#64 |||
        BitVec.setWidth 64 ((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v)))).rotateLeft 8))))).toNat
      = v % 256 * 256 + v / 256 := by
  have h := bswap16 v hv
  have h2 : v % 256 * 256 + v / 256 < 65536 := by omega
  have e1 : (v % 256 * 256 + v / 256) % 65536 = v % 256 * 256 + v / 256 := Nat.mod_eq_of_lt h2
  have e2 : (v % 256 * 256 + v / 256) % 4294967296 = v % 256 * 256 + v / 256 := Nat.mod_eq_of_lt (Nat.lt_trans h2 (by decide))
  have e3 : (v % 256 * 256 + v / 256) % 18446744073709551616 = v % 256 * 256 + v / 256 := Nat.mod_eq_of_lt (Nat.lt_trans h2 (by decide))
  simp only [BitVec.toNat_setWidth, h, e1, e2, e3, Nat.reducePow]

theorem bswap16x (v : Nat) (hv : v < 65536) :
    (((BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v))) &&& 18446744073709486080#64).toNat |||
      (((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v)))).rotateLeft 8).toNat % 18446744073709551616))
      = v % 256 * 256 + v / 256 := by
  have := bswap16m v hv
  have h : ((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v)))).rotateLeft 8).toNat % 18446744073709551616 =
      ((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v)))).rotateLeft 8).toNat :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))
  rwa [← h] at this


-- SRsh helpers
theorem srsh_core (X n : Nat) (hX : X < 2 ^ 256) (hn : n ≤ 256) :
    2 ^ 256 - 1 - (2 ^ 256 - 1 - X) / 2 ^ n = X / 2 ^ n + (2 ^ 256 - 2 ^ (256 - n)) := by
  have hd : 0 < 2 ^ n := Nat.two_pow_pos n
  have hde : 2 ^ n * 2 ^ (256 - n) = 2 ^ 256 := by
    rw [← Nat.pow_add, show n + (256 - n) = 256 by omega]
  generalize hD : 2 ^ n = d at *
  generalize hE : 2 ^ (256 - n) = e at *
  generalize (2:Nat) ^ 256 = Wv at *
  have hq : X / d < e := by
    rw [Nat.div_lt_iff_lt_mul hd, Nat.mul_comm, hde]; exact hX
  have h1 := Nat.div_add_mod X d
  have h2 := Nat.mod_lt X hd
  generalize X / d = q at *
  generalize X % d = r at *
  have heW : e ≤ Wv := by rw [← hde]; exact Nat.le_mul_of_pos_left e hd
  obtain ⟨k, hk⟩ : ∃ k, e = q + 1 + k := ⟨e - q - 1, by omega⟩
  subst hk
  have hW : Wv = d * q + d + d * k := by rw [← hde, Nat.mul_add, Nat.mul_add, Nat.mul_one]
  have : (Wv - 1 - X) / d = k := by
    apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_comm]; omega
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega
  rw [this]
  omega

theorem srsh_pos (X n : Nat) (h : X < 2 ^ 255) : Spec.srsh X n = Spec.rsh X n := by
  have : Spec.W / 2 = 2 ^ 255 := by decide
  simp only [Spec.srsh, Spec.rsh, this, if_pos h]

theorem srsh_pos' (X n : Nat) (h : X < 2 ^ 255) : Spec.srsh X n = X / 2 ^ n := srsh_pos X n h

theorem srsh_neg_big (X n : Nat) (hX : X < 2 ^ 256) (hn : 256 ≤ n) (h : 2 ^ 255 ≤ X) : Spec.srsh X n = 2 ^ 256 - 1 := by
  have : Spec.W / 2 = 2 ^ 255 := by decide
  have hlt : (2 ^ 256 - 1 - X) / 2 ^ n = 0 := by
    apply Nat.div_eq_of_lt
    calc 2 ^ 256 - 1 - X < 2 ^ 256 := by omega
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  simp only [Spec.srsh, this, show ¬ (X < 2 ^ 255) from by omega, if_false]
  simp only [Spec.W]
  rw [hlt]

theorem srsh_neg (X n : Nat) (hX : X < 2 ^ 256) (hn : n ≤ 256) (h : 2 ^ 255 ≤ X) :
    Spec.srsh X n = X / 2 ^ n + (2 ^ 256 - 2 ^ (256 - n)) := by
  have : Spec.W / 2 = 2 ^ 255 := by decide
  simp only [Spec.srsh, this, show ¬ (X < 2 ^ 255) from by omega, if_false]
  exact srsh_core X n hX hn


theorem sign_iff (a : Nat) (ha : a < 18446744073709551616) :
    ((BitVec.ofNat 64 a).getLsbD 63 == false) = decide (a < 9223372036854775808) := by
  rw [BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq]
  have h : a / 2 ^ 63 < 2 := by omega
  have h2 : a / 2 ^ 63 % 2 = a / 2 ^ 63 := Nat.mod_eq_of_lt h
  by_cases hc : a < 9223372036854775808
  · have : a / 2 ^ 63 = 0 := by omega
    simp [this, hc]
  · have : a / 2 ^ 63 = 1 := by omega
    simp [this, hc]

theorem msb_pos (a : Nat) (ha : a < 18446744073709551616) (h : ((BitVec.ofNat 64 a).getLsbD 63 == false) = true) : a < 9223372036854775808 := by
  rw [sign_iff a ha] at h; simpa using h
theorem msb_neg (a : Nat) (ha : a < 18446744073709551616) (h : ¬((BitVec.ofNat 64 a).getLsbD 63 == false) = true) : 9223372036854775808 ≤ a := by
  rw [sign_iff a ha] at h; simpa using h

theorem mask_val (r : Nat) (hr : 0 < r) (hr2 : r < 64) :
    (if 64 - r < 64 then -BitVec.ofNat 64 (2 ^ ((64 - r) % 64)) else 0#64).toNat =
      18446744073709551616 - 2 ^ (64 - r) := by
  have hc : 64 - r < 64 := by omega
  simp only [hc, if_true, BitVec.toNat_neg, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 64 - r < 64)]
  have hp : 2 ^ (64 - r) < 18446744073709551616 := by
    calc 2 ^ (64 - r) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
      _ = 18446744073709551616 := by decide
  have hq : 2 ^ (64 - r) % 18446744073709551616 = 2 ^ (64 - r) := Nat.mod_eq_of_lt hp
  show (2 ^ 64 - 2 ^ (64 - r) % 2 ^ 64) % 2 ^ 64 = _
  have h64 : (2:Nat) ^ 64 = 18446744073709551616 := by decide
  rw [h64, hq]
  have := Nat.two_pow_pos (64 - r)
  omega

theorem top_val (a r : Nat) (ha : a < 18446744073709551616) (hr : r < 64) :
    (a / 2 ^ r ||| (if 64 - r < 64 then -BitVec.ofNat 64 (2 ^ ((64 - r) % 64)) else 0#64).toNat) % 18446744073709551616 =
      a / 2 ^ r + (18446744073709551616 - 2 ^ (64 - r)) := by
  by_cases h0 : r = 0
  · subst h0
    simp only [show ¬ (64 - 0 < 64) from by decide, if_false, BitVec.toNat_ofNat, Nat.pow_zero, Nat.div_one, if_true]
    have e : (18446744073709551616 : Nat) - 2 ^ (64 - 0) = 0 := by decide
    rw [e]
    show (a ||| 0) % _ = a + 0
    simp [Nat.mod_eq_of_lt ha]
  · rw [mask_val r (by omega) hr]
    have h := pq_eq r (by omega)
    have hP : 0 < 2 ^ r := Nat.two_pow_pos r
    have hS : 0 < 2 ^ (64 - r) := Nat.two_pow_pos _
    have hv : a / 2 ^ r < 2 ^ (64 - r) := by
      rw [Nat.div_lt_iff_lt_mul hP, Nat.mul_comm, h]; exact ha
    have hm : 18446744073709551616 - 2 ^ (64 - r) = (2 ^ r - 1) * 2 ^ (64 - r) := by
      rw [Nat.sub_mul, Nat.one_mul, h]
    rw [hm, or_hi _ _ _ hv]
    have : (2 ^ r - 1) * 2 ^ (64 - r) + 2 ^ (64 - r) = 18446744073709551616 := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hP, h]
    apply Nat.mod_eq_of_lt
    omega

theorem pw_le (t : Nat) (ht : t ≤ 64) : 2 ^ (64 - t) ≤ 18446744073709551616 := by
  calc 2 ^ (64 - t) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 18446744073709551616 := by decide

theorem sub_aux (lo t : Nat) (ht : t < 64) (hlo : lo ≤ 192) :
    18446744073709551616 - (lo + t) - (18446744073709551616 - lo - 64) = 64 - t := by omega

theorem sub_aux2 (t : Nat) (ht : t < 64) :
    18446744073709551616 - t - 18446744073709551552 = 64 - t := by omega

theorem msb_f (a : Nat) (ha : a < 18446744073709551616) (h : a < 9223372036854775808) :
    (BitVec.ofNat 64 a).getLsbD 63 = false := by
  have := sign_iff a ha
  simp [h] at this
  exact this

theorem msb_t (a : Nat) (ha : a < 18446744073709551616) (h : 9223372036854775808 ≤ a) :
    (BitVec.ofNat 64 a).getLsbD 63 = true := by
  have := sign_iff a ha
  have h2 : ¬ (a < 9223372036854775808) := by omega
  simp [h2] at this
  exact this

theorem top_amd (a n : Nat) (ha : a < 18446744073709551616) (hn : n % 64 ≠ 0) (hn2 : n < 18446744073709551616) :
    ((18446744073709551615#64 <<< ((18446744073709551616 - n) % 64) &&&
        (if 18446744073709551616 - (18446744073709551552 + n % 64) < 64 then 18446744073709551615#64 else 0#64)) |||
      BitVec.ofNat 64 a >>> (n % 64)).toNat = a / 2 ^ (n % 64) + (18446744073709551616 - 2 ^ (64 - n % 64)) := by
  have hr1 : 1 ≤ n % 64 := by omega
  have hr2 : n % 64 < 64 := by omega
  generalize hr : n % 64 = r at *
  have hs : (18446744073709551616 - n) % 64 = 64 - r := by omega
  have hc : 18446744073709551616 - (18446744073709551552 + r) < 64 := by omega
  rw [hs]
  simp only [hc, ite_true]
  rw [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hP : 2 ^ (64 - r) ≤ 18446744073709551616 := pw_le r (by omega)
  have h := pq_eq r (by omega)
  have hP0 : 0 < 2 ^ r := Nat.two_pow_pos r
  have hS0 : 0 < 2 ^ (64 - r) := Nat.two_pow_pos _
  simp only [Nat.reducePow, Nat.reduceMod, BitVec.toNat_ofNat]
  have hm : 18446744073709551615 * 2 ^ (64 - r) % 18446744073709551616 = 18446744073709551616 - 2 ^ (64 - r) := by
    generalize 2 ^ (64 - r) = P at *
    omega
  rw [hm, and_ones_lt _ (by omega)]
  have hv : a % 18446744073709551616 / 2 ^ r < 2 ^ (64 - r) := by
    rw [Nat.mod_eq_of_lt ha, Nat.div_lt_iff_lt_mul hP0, Nat.mul_comm, h]; exact ha
  have hm2 : 18446744073709551616 - 2 ^ (64 - r) = (2 ^ r - 1) * 2 ^ (64 - r) := by
    rw [Nat.sub_mul, Nat.one_mul, h]
  rw [Nat.mod_eq_of_lt ha] at hv ⊢
  rw [Nat.or_comm, hm2, or_hi _ _ _ hv]

theorem rot3_idx' (b : Nat) (hb : b < 18446744073709551616) :
    ((BitVec.ofNat 64 b).rotateRight 3).toNat % 2305843009213693952 = b / 8 := by
  rw [BitVec.toNat_rotateRight, BitVec.toNat_ofNat]
  simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceSub, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt hb]
  have h := rot3_idx b hb
  have hl : (b / 8 ||| b * 2305843009213693952 % 18446744073709551616) < 18446744073709551616 :=
    Nat.or_lt_two_pow (n := 64) (by omega) (by omega)
  rw [Nat.mod_eq_of_lt hl] at h
  exact h


-- ExtendSign helpers
theorem rr0 (x : BitVec 64) : x.rotateRight 0 = x := by
  simp [BitVec.rotateRight, BitVec.rotateRightAux]

theorem es_neg_mask (sh : Nat) (h : sh < 64) :
    (~~~(-BitVec.ofNat 64 (2 ^ sh))).toNat = 2 ^ sh - 1 := by
  rw [BitVec.toNat_not, BitVec.toNat_neg, BitVec.toNat_ofNat]
  have hP : 2 ^ sh < 18446744073709551616 := by
    calc 2 ^ sh < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) h
      _ = 18446744073709551616 := by decide
  have hP0 := Nat.two_pow_pos sh
  have h64 : (2:Nat) ^ 64 = 18446744073709551616 := by decide
  rw [h64]
  generalize 2 ^ sh = P at *
  omega

theorem es_bit7 (L sh : Nat) (h : sh ≤ 56) :
    (if (BitVec.ofNat 64 L >>> sh).getLsbD 7 = true then 18446744073709551615#64 else 0#64).toNat =
      if L / 2 ^ (sh + 7) % 2 = 1 then 18446744073709551615 else 0 := by
  have hb : (BitVec.ofNat 64 L >>> sh).getLsbD 7 = decide (L / 2 ^ (sh + 7) % 2 = 1) := by
    rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq]
    have : sh + 7 < 64 := by omega
    simp [this]
  rw [hb]
  by_cases hc : L / 2 ^ (sh + 7) % 2 = 1
  · simp [hc]
  · simp [hc]

theorem es_rot0 (L sh : Nat) (hL : L < 18446744073709551616) :
    ((BitVec.ofNat 64 L >>> sh).rotateRight 0).toNat = L / 2 ^ sh := by
  rw [rr0, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  simp only [Nat.reducePow, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hL]

theorem es_core (L sh : Nat) (hL : L < 18446744073709551616) (h : sh ≤ 56) (A : Nat)
    (hA : A = (if L / 2 ^ (sh + 7) % 2 = 1 then 18446744073709551360 else 0) + L / 2 ^ sh % 256) :
    (L % 2 ^ sh ||| 2 ^ sh * A % 18446744073709551616) % 18446744073709551616 =
      L % 2 ^ (sh + 8) + (if L / 2 ^ (sh + 7) % 2 = 1 then 18446744073709551616 - 2 ^ (sh + 8) else 0) := by
  have hP0 := Nat.two_pow_pos sh
  have hQ := pq_eq sh (by omega)
  have hQ0 := Nat.two_pow_pos (64 - sh)
  have hPow : 2 ^ (sh + 8) = 2 ^ sh * 256 := by rw [Nat.pow_add]
  have hQ256 : 256 ≤ 2 ^ (64 - sh) := by
    have : 2 ^ 8 ≤ 2 ^ (64 - sh) := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  have hmod : L % 2 ^ (sh + 8) = L % 2 ^ sh + 2 ^ sh * (L / 2 ^ sh % 256) := by
    rw [hPow, Nat.mod_mul]
  have hbyte : L / 2 ^ sh % 256 < 256 := Nat.mod_lt _ (by decide)
  have hlo : L % 2 ^ sh < 2 ^ sh := Nat.mod_lt _ hP0
  have hsb : L / 2 ^ (sh + 7) % 2 = L / 2 ^ sh / 128 % 2 := by
    rw [Nat.pow_add, Nat.div_div_eq_div_mul]
  have hmodsh := shl_lo
  by_cases hs : L / 2 ^ (sh + 7) % 2 = 1
  · subst hA
    simp only [hs, ite_true]
    rw [Nat.mul_comm (2 ^ sh), shl_lo _ sh (by omega)]
    obtain ⟨T, hT⟩ : ∃ T, 2 ^ sh = T + 1 := ⟨2 ^ sh - 1, by omega⟩
    have hQT : 2 ^ (64 - sh) * T + 2 ^ (64 - sh) = 18446744073709551616 := by
      rw [← hQ, hT, Nat.add_mul, Nat.one_mul, Nat.mul_comm (2 ^ (64 - sh)) T]
    have hv : (18446744073709551360 + L / 2 ^ sh % 256) % 2 ^ (64 - sh) = 2 ^ (64 - sh) - 256 + L / 2 ^ sh % 256 := by
      have : 18446744073709551360 + L / 2 ^ sh % 256 = (2 ^ (64 - sh) - 256 + L / 2 ^ sh % 256) + 2 ^ (64 - sh) * T := by
        omega
      rw [this, Nat.add_mul_mod_self_left]
      apply Nat.mod_eq_of_lt
      omega
    rw [hv]
    generalize hqq : 2 ^ (64 - sh) = Q at *
    generalize hbb : L / 2 ^ sh % 256 = byte at *
    generalize hlo' : L % 2 ^ sh = lo at *
    rw [Nat.mul_comm (2 ^ sh) (Q - 256 + byte)]
    rw [or_hi lo _ sh hlo]
    have hmul : (Q - 256 + byte) * 2 ^ sh = 18446744073709551616 - 2 ^ sh * 256 + byte * 2 ^ sh := by
      rw [Nat.add_mul, Nat.sub_mul, Nat.mul_comm Q, hQ, Nat.mul_comm 256]
    rw [hmul, hmod, hPow, Nat.mul_comm byte]
    have hP256 : 2 ^ sh * 256 ≤ 18446744073709551616 := by
      have := Nat.mul_le_mul_left (2 ^ sh) hQ256
      omega
    have hBP : 2 ^ sh * byte + 2 ^ sh ≤ 2 ^ sh * 256 := by
      have := Nat.mul_le_mul_left (2 ^ sh) (show byte + 1 ≤ 256 by omega)
      rw [Nat.mul_add, Nat.mul_one] at this
      exact this
    generalize 2 ^ sh * byte = PB at *
    generalize 2 ^ sh * 256 = P256 at *
    generalize 2 ^ sh = P at *
    omega
  · subst hA
    simp only [hs, ite_false, Nat.zero_add]
    have hBP : 2 ^ sh * (L / 2 ^ sh % 256) + 2 ^ sh ≤ 2 ^ sh * 256 := by
      have := Nat.mul_le_mul_left (2 ^ sh) (show L / 2 ^ sh % 256 + 1 ≤ 256 by omega)
      rw [Nat.mul_add, Nat.mul_one] at this
      exact this
    have hP256 : 2 ^ sh * 256 ≤ 18446744073709551616 := by
      have := Nat.mul_le_mul_left (2 ^ sh) hQ256
      omega
    rw [Nat.mod_eq_of_lt (by omega : 2 ^ sh * (L / 2 ^ sh % 256) < 18446744073709551616)]
    rw [Nat.mul_comm (2 ^ sh), or_hi _ _ _ hlo, Nat.mul_comm, hmod]
    rw [Nat.mod_eq_of_lt (by omega)]
    rfl


theorem es_E (L sh : Nat) (hL : L < 18446744073709551616) (h : sh ≤ 56) :
    (L &&& (~~~(-BitVec.ofNat 64 (2 ^ sh))).toNat ||| 2 ^ sh * ((if (BitVec.ofNat 64 L >>> sh).getLsbD 7 = true then 18446744073709551615#64 else 0#64).toNat &&& 18446744073709551360 ||| ((BitVec.ofNat 64 L >>> sh).rotateRight 0).toNat % 256) % 18446744073709551616) % 18446744073709551616 =
      L % 2 ^ (sh + 8) + (if L / 2 ^ (sh + 7) % 2 = 1 then 18446744073709551616 - 2 ^ (sh + 8) else 0) := by
  rw [es_neg_mask sh (by omega), es_bit7 L sh h, es_rot0 L sh hL, Nat.and_two_pow_sub_one_eq_mod]
  have hbyte : L / 2 ^ sh % 256 < 256 := Nat.mod_lt _ (by decide)
  apply es_core L sh hL h
  by_cases hs : L / 2 ^ (sh + 7) % 2 = 1
  · simp only [hs, ite_true]
    have e1 : (18446744073709551615 &&& 18446744073709551360) = 18446744073709551360 := by decide
    rw [e1, Nat.or_comm, show (18446744073709551360 : Nat) = 72057594037927935 * 2 ^ 8 from rfl, or_hi _ _ _ (by simpa using hbyte)]
    omega
  · simp only [hs, ite_false]
    have e1 : (0 &&& 18446744073709551360) = 0 := by decide
    rw [e1, Nat.zero_or]
    omega



theorem es_sb (L sh : Nat) (hL : L < 18446744073709551616) (h : sh ≤ 56) :
    ((if (BitVec.ofNat 64 L >>> sh).getLsbD 7 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551360#64 |||
      (BitVec.ofNat 64 L >>> sh).rotateRight 0 &&& 255#64 &&& 255#64).toNat =
      (if L / 2 ^ (sh + 7) % 2 = 1 then 18446744073709551360 else 0) + L / 2 ^ sh % 256 := by
  simp only [BitVec.toNat_or, BitVec.toNat_and]
  rw [es_bit7 L sh h, es_rot0 L sh hL]
  have e255 : 255 = 2 ^ 8 - 1 := by decide
  have hb : L / 2 ^ sh % 256 < 256 := Nat.mod_lt _ (by decide)
  have eb : L / 2 ^ sh &&& 255 &&& 255 = L / 2 ^ sh % 256 := by
    rw [e255, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
    simp
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [eb]
  by_cases hs : L / 2 ^ (sh + 7) % 2 = 1
  · simp only [hs, ite_true]
    have e1 : (18446744073709551615 &&& 18446744073709551360) = 18446744073709551360 := by decide
    rw [e1, Nat.or_comm, show (18446744073709551360 : Nat) = 72057594037927935 * 2 ^ 8 from rfl, or_hi _ _ _ (by simpa using hb)]
    omega
  · simp only [hs, ite_false]
    have e1 : (0 &&& 18446744073709551360) = 0 := by decide
    rw [e1, Nat.zero_or]
    omega

theorem es_fill (S : BitVec 64) (c : Prop) [Decidable c] (b : Nat) (hb : b < 256)
    (hS : S.toNat = (if c then 18446744073709551360 else 0) + b) :
    ((if S.getLsbD 63 = true then 18446744073709551615#64 else 0#64).toNat &&& 18374686479671623680 |||
      (S.rotateRight 8).toNat % 72057594037927936) % 18446744073709551616 =
      if c then 18446744073709551615 else 0 := by
  have hbit : S.getLsbD 63 = decide (S.toNat / 2 ^ 63 % 2 = 1) := by
    rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
  rw [BitVec.toNat_rotateRight]
  simp only [Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceSub]
  by_cases hc : c
  · simp only [hc, ite_true] at hS ⊢
    have hbt : S.getLsbD 63 = true := by
      rw [hbit]; simp only [hS]; simp; omega
    simp only [hbt, ite_true]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    have e1 : (18446744073709551615 &&& 18374686479671623680) = 18374686479671623680 := by decide
    rw [e1]
    have h1 : S.toNat / 256 = 72057594037927935 := by omega
    have h2 : S.toNat * 72057594037927936 % 18446744073709551616 = (b % 256) * 72057594037927936 := by omega
    rw [h1, h2]
    have hor : (72057594037927935 ||| (b % 256) * 72057594037927936) % 72057594037927936 = 72057594037927935 := by
      have := or_hi 72057594037927935 (b % 256) 56 (by decide)
      simp only [Nat.reducePow] at this
      rw [this]; omega
    rw [hor]
    decide
  · simp only [hc, ite_false] at hS ⊢
    have hbt : S.getLsbD 63 = false := by
      rw [hbit]; simp only [hS]; simp; omega
    simp only [hbt]
    simp only [Bool.false_eq_true, ite_false, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    have h1 : S.toNat / 256 = 0 := by omega
    have h2 : S.toNat * 72057594037927936 % 18446744073709551616 = (b % 256) * 72057594037927936 := by omega
    rw [h1, h2]
    have e1 : (0 &&& 18374686479671623680) = 0 := by decide
    have hor : (0 ||| (b % 256) * 72057594037927936) % 72057594037927936 = 0 := by
      rw [Nat.zero_or]; exact Nat.mul_mod_left _ _
    simp only [Nat.zero_and, Nat.zero_or]
    rw [Nat.mul_mod_left]

theorem es_F (L sh : Nat) (hL : L < 18446744073709551616) (h : sh ≤ 56) :
    ((if ((if (BitVec.ofNat 64 L >>> sh).getLsbD 7 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551360#64 ||| (BitVec.ofNat 64 L >>> sh).rotateRight 0 &&& 255#64 &&& 255#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64).toNat &&& 18374686479671623680 ||| (((if (BitVec.ofNat 64 L >>> sh).getLsbD 7 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551360#64 ||| (BitVec.ofNat 64 L >>> sh).rotateRight 0 &&& 255#64 &&& 255#64).rotateRight 8).toNat % 72057594037927936) % 18446744073709551616 =
      if L / 2 ^ (sh + 7) % 2 = 1 then 18446744073709551615 else 0 :=
  es_fill _ (L / 2 ^ (sh + 7) % 2 = 1) (L / 2 ^ sh % 256) (Nat.mod_lt _ (by decide)) (es_sb L sh hL h)


theorem or3_zero (a b c : Nat) (h : a ||| (b ||| c) = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have h1 := Nat.or_eq_zero_iff.mp h
  have h2 := Nat.or_eq_zero_iff.mp h1.2
  exact ⟨h1.1, h2.1, h2.2⟩
theorem or3_ne (a b c : Nat) (h : ¬ a ||| (b ||| c) = 0) : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 := by
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · by_cases hc : c = 0
      · subst ha hb hc; exact absurd rfl h
      · exact Or.inr (Or.inr hc)
    · exact Or.inr (Or.inl hb)
  · exact Or.inl ha

-- ExtendSign amd64 helpers
theorem sxv (V : BitVec 64) :
    (BitVec.signExtend 64 (BitVec.setWidth 8 V)).toNat =
      V.toNat % 256 + (if V.toNat / 128 % 2 = 1 then 18446744073709551616 - 256 else 0) := by
  rw [BitVec.toNat_signExtend]
  have hx8 : (BitVec.setWidth 8 V).toNat = V.toNat % 256 := by
    rw [BitVec.toNat_setWidth]
  have hm : (BitVec.setWidth 8 V).msb = decide (V.toNat / 128 % 2 = 1) := by
    rw [BitVec.msb_eq_decide, hx8]
    simp only [Nat.reduceSub, Nat.reducePow]
    by_cases h : V.toNat / 128 % 2 = 1
    · have : 128 ≤ V.toNat % 256 := by omega
      simp [h, this]
    · have : ¬ 128 ≤ V.toNat % 256 := by omega
      simp [h, this]
  rw [hm, BitVec.toNat_setWidth, hx8]
  have : V.toNat % 256 % 2 ^ 64 = V.toNat % 256 := Nat.mod_eq_of_lt (by omega)
  rw [this]
  by_cases h : V.toNat / 128 % 2 = 1
  · simp [h]
  · simp [h]

theorem sxs (V : BitVec 64) :
    ((BitVec.signExtend 64 (BitVec.setWidth 8 V)).sshiftRight 8).toNat =
      if V.toNat / 128 % 2 = 1 then 18446744073709551615 else 0 := by
  have hv := sxv V
  have hb : V.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  rw [BitVec.toNat_sshiftRight, BitVec.msb_eq_decide]
  by_cases h : V.toNat / 128 % 2 = 1
  · simp only [h, ite_true] at hv ⊢
    have h1 : 2 ^ (64 - 1) ≤ (BitVec.signExtend 64 (BitVec.setWidth 8 V)).toNat := by
      simp only [Nat.reduceSub, Nat.reducePow]; omega
    simp only [h1, decide_true, ite_true]
    rw [hv, Nat.shiftRight_eq_div_pow]
    simp only [Nat.reducePow]
    omega
  · simp only [h, ite_false] at hv ⊢
    have h1 : ¬ 2 ^ (64 - 1) ≤ (BitVec.signExtend 64 (BitVec.setWidth 8 V)).toNat := by
      simp only [Nat.reduceSub, Nat.reducePow]; omega
    simp only [h1, decide_false, Bool.false_eq_true, ite_false]
    rw [hv, Nat.shiftRight_eq_div_pow]
    simp only [Nat.reducePow]
    omega

theorem es_Va (L sh : Nat) (hL : L < 18446744073709551616) :
    (BitVec.ofNat 64 L >>> sh).toNat = L / 2 ^ sh := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  simp only [Nat.reducePow, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hL]

theorem es_Ea (L sh : Nat) (hL : L < 18446744073709551616) (h : sh ≤ 56) :
    (~~~(18446744073709551615#64 <<< sh) &&& BitVec.ofNat 64 L |||
      BitVec.signExtend 64 (BitVec.setWidth 8 (BitVec.ofNat 64 L >>> sh)) <<< sh).toNat =
      L % 2 ^ (sh + 8) + (if L / 2 ^ (sh + 7) % 2 = 1 then 18446744073709551616 - 2 ^ (sh + 8) else 0) := by
  have hv := sxv (BitVec.ofNat 64 L >>> sh)
  rw [es_Va L sh hL] at hv
  have hsb : L / 2 ^ sh / 128 % 2 = L / 2 ^ (sh + 7) % 2 := by
    rw [Nat.pow_add, Nat.div_div_eq_div_mul]
  rw [hsb] at hv
  simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceSub, Nat.mod_eq_of_lt hL]
  rw [hv]
  have hP0 := Nat.two_pow_pos sh
  have hP : 2 ^ sh ≤ 18446744073709551616 := by
    calc 2 ^ sh ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 18446744073709551616 := by decide
  have hm : 18446744073709551615 * 2 ^ sh % 18446744073709551616 = 18446744073709551616 - 2 ^ sh := by
    generalize 2 ^ sh = P at *
    omega
  have hmask : 18446744073709551615 - 18446744073709551615 % 18446744073709551616 * 2 ^ sh % 18446744073709551616 = 2 ^ sh - 1 := by
    rw [show (18446744073709551615 : Nat) % 18446744073709551616 = 18446744073709551615 from by decide, hm]
    omega
  rw [hmask, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  have key := es_core L sh hL h ((L / 2 ^ sh % 256 + if L / 2 ^ (sh + 7) % 2 = 1 then 18446744073709551616 - 256 else 0))
    (by by_cases hs : L / 2 ^ (sh + 7) % 2 = 1 <;> simp [hs] <;> omega)
  rw [Nat.mul_comm (L / 2 ^ sh % 256 + _) (2 ^ sh)]
  have hlt : (L % 2 ^ sh ||| 2 ^ sh * (L / 2 ^ sh % 256 + if L / 2 ^ (sh + 7) % 2 = 1 then 18446744073709551616 - 256 else 0) % 18446744073709551616) < 18446744073709551616 := by
    have h1 : L % 2 ^ sh < 2 ^ 64 := by
      have := Nat.mod_lt L hP0; omega
    exact Nat.or_lt_two_pow (n := 64) h1 (Nat.mod_lt _ (by decide))
  rw [Nat.mod_eq_of_lt hlt] at key
  exact key

theorem es_Ea0 (L : Nat) (hL : L < 18446744073709551616) :
    (0#64 &&& BitVec.ofNat 64 L ||| BitVec.signExtend 64 (BitVec.setWidth 8 (BitVec.ofNat 64 L))).toNat =
      L % 256 + (if L / 128 % 2 = 1 then 18446744073709551616 - 256 else 0) := by
  have hv := sxv (BitVec.ofNat 64 L)
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_eq_of_lt hL] at hv
  rw [BitVec.toNat_or, BitVec.toNat_and, hv]
  simp only [BitVec.toNat_zero, Nat.zero_and, Nat.zero_or]

theorem es_Fa (L sh : Nat) (hL : L < 18446744073709551616) :
    ((BitVec.signExtend 64 (BitVec.setWidth 8 (BitVec.ofNat 64 L >>> sh))).sshiftRight 8).toNat =
      if L / 2 ^ (sh + 7) % 2 = 1 then 18446744073709551615 else 0 := by
  have hv := sxs (BitVec.ofNat 64 L >>> sh)
  have hsb : L / 2 ^ sh / 128 % 2 = L / 2 ^ (sh + 7) % 2 := by
    rw [Nat.pow_add, Nat.div_div_eq_div_mul]
  rw [es_Va L sh hL, hsb] at hv
  exact hv

theorem es_Fa0 (L : Nat) (hL : L < 18446744073709551616) :
    ((BitVec.signExtend 64 (BitVec.setWidth 8 (BitVec.ofNat 64 L))).sshiftRight 8).toNat =
      if L / 128 % 2 = 1 then 18446744073709551615 else 0 := by
  have hv := sxs (BitVec.ofNat 64 L)
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_eq_of_lt hL] at hv
  exact hv

theorem bvor3 (a b c : Nat) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616)
    (hc : c < 18446744073709551616) :
    (BitVec.ofNat 64 a ||| BitVec.ofNat 64 b ||| BitVec.ofNat 64 c).toNat = a ||| b ||| c := by
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc]

theorem or3l_iff (a b c : Nat) : (a ||| b ||| c = 0) ↔ (a = 0 ∧ b = 0 ∧ c = 0) := by
  constructor
  · intro h
    have h1 := Nat.or_eq_zero_iff.mp h
    have h2 := Nat.or_eq_zero_iff.mp h1.1
    exact ⟨h2.1, h2.2, h1.2⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

-- ByteLen helpers
def blS (u : BitVec 64) : BitVec 64 :=
  ((if u.getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 |||
      u.rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 61

theorem blS_zero (u : BitVec 64) (hu : u.toNat < 2 ^ 63) : blS u = 0#64 := by
  have hb : u.getLsbD 63 = false := by
    rw [← BitVec.testBit_toNat]
    exact Nat.testBit_lt_two_pow (by omega)
  apply BitVec.eq_of_toNat_eq
  unfold blS
  simp only [hb, Bool.false_eq_true, ite_false, BitVec.toNat_ushiftRight, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_rotateRight]
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]
  have h1 : u.toNat / 9223372036854775808 = 0 := by omega
  have h2 : u.toNat * 2 % 18446744073709551616 = u.toNat * 2 := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, Nat.zero_or]
  have h3 : u.toNat * 2 &&& 18446744073709551615 = u.toNat * 2 := Nat.and_two_pow_sub_one_of_lt_two_pow (n := 64) (by omega)
  rw [h3, Nat.and_one_is_mod, Nat.zero_and, Nat.zero_or]
  omega

theorem bl_trick (v u : BitVec 64) (huv : u = v + 7#64) (hv : v.toNat ≤ 256) :
    ((if (v + blS u + 7#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64).toNat &&& 16140901064495857664 |||
      ((v + blS u + 7#64).rotateRight 3).toNat % 2305843009213693952) = (v.toNat + 7) / 8 := by
  have hu : u.toNat = v.toNat + 7 := by
    rw [huv, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  rw [blS_zero u (by omega)]
  have hw : v + 0#64 + 7#64 = u := by rw [huv]; simp
  rw [hw]
  have hb : u.getLsbD 63 = false := by
    rw [← BitVec.testBit_toNat]
    exact Nat.testBit_lt_two_pow (by omega)
  simp only [hb, Bool.false_eq_true, ite_false, BitVec.toNat_rotateRight, hu]
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]
  have h4 : (v.toNat + 7) * 2305843009213693952 % 18446744073709551616 = ((v.toNat + 7) % 8) * 2305843009213693952 := by omega
  have hor := Fv256.Util.or_hi ((v.toNat + 7) / 8) ((v.toNat + 7) % 8) 61 (by simp only [Nat.reducePow]; omega)
  simp only [Nat.reducePow] at hor
  rw [Nat.zero_and, Nat.zero_or, h4, hor]
  omega

-- Bytes20 helpers
section B20
open Janus.Arm64
theorem b20_res (M0 : Memory) (sp A B V2 : Nat) :
    Fv256.Spec.fromBE (fun i => ((((M0.writeLE (sp + 8) 8 A).writeLE (sp + 16) 8 B).writeLE (sp + 20) 8 V2).readLE (sp + 8 + i) 1)) 20 =
      Janus.Arm64.revBytesNat 4 (A % 4294967296) * 2 ^ 128 +
      Janus.Arm64.revBytesNat 8 (A / 4294967296 % 4294967296 + 4294967296 * (B % 4294967296)) * 2 ^ 64 +
      Janus.Arm64.revBytesNat 8 (V2 % 18446744073709551616) := by
  rw [Util.be20_rev]
  obtain ⟨M, hM⟩ : ∃ M, M = (((M0.writeLE (sp + 8) 8 A).writeLE (sp + 16) 8 B).writeLE (sp + 20) 8 V2) := ⟨_, rfl⟩
  rw [← hM]
  have h4 : M.readLE (sp + 8) 4 = A % 4294967296 := by
    rw [hM, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_inside _ _ (by omega) (by omega)]
    simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one]
  have h12 : M.readLE (sp + 12) 4 = A / 4294967296 % 4294967296 := by
    rw [hM, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_inside _ _ (by omega) (by omega)]
    have : sp + 12 - (sp + 8) = 4 := by omega
    rw [this]
  have h16 : M.readLE (sp + 16) 4 = B % 4294967296 := by
    rw [hM, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_inside _ _ (by omega) (by omega)]
    simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one]
  have h20 : M.readLE (sp + 20) 8 = V2 % 18446744073709551616 := by
    rw [hM, Memory.readLE_writeLE_self]
  have h8 : M.readLE (sp + 8 + 4) 8 = M.readLE (sp + 8 + 4) 4 + 256 ^ 4 * M.readLE (sp + 8 + 4 + 4) 4 := Memory.readLE_add _ _ 4 4
  have e12 : sp + 8 + 4 = sp + 12 := by omega
  have e16 : sp + 8 + 4 + 4 = sp + 16 := by omega
  have e20 : sp + 8 + 12 = sp + 20 := by omega
  rw [h8, e12, e16, e20, h4, h12, h16, h20]

theorem b20_locA0 (base : Memory) (q V0 V1 : Nat) :
    (((base.writeLE q 4 V0).writeLE (q + 4) 8 V1).readLE q 8) =
      V0 % 4294967296 + 4294967296 * (V1 % 4294967296) := by
  have h8 : (((base.writeLE q 4 V0).writeLE (q + 4) 8 V1).readLE q 8) =
      (((base.writeLE q 4 V0).writeLE (q + 4) 8 V1).readLE q 4) +
        256 ^ 4 * (((base.writeLE q 4 V0).writeLE (q + 4) 8 V1).readLE (q + 4) 4) := Memory.readLE_add _ _ 4 4
  rw [h8, Memory.readLE_writeLE_of_disjoint _ _ (by omega),
    Memory.readLE_writeLE_self, Memory.readLE_writeLE_inside _ _ (by omega) (by omega)]
  simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.reducePow]

theorem b20_locB0 (base : Memory) (q V0 V1 V2 : Nat) :
    ((((base.writeLE q 4 V0).writeLE (q + 4) 8 V1).writeLE (q + 12) 8 V2).readLE (q + 8) 8) =
      V1 / 4294967296 % 4294967296 + 4294967296 * (V2 % 4294967296) := by
  have h8 : ((((base.writeLE q 4 V0).writeLE (q + 4) 8 V1).writeLE (q + 12) 8 V2).readLE (q + 8) 8) =
      ((((base.writeLE q 4 V0).writeLE (q + 4) 8 V1).writeLE (q + 12) 8 V2).readLE (q + 8) 4) +
        256 ^ 4 * ((((base.writeLE q 4 V0).writeLE (q + 4) 8 V1).writeLE (q + 12) 8 V2).readLE (q + 8 + 4) 4) := Memory.readLE_add _ _ 4 4
  rw [h8, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_inside _ _ (by omega) (by omega),
    Memory.readLE_writeLE_inside _ _ (by omega) (by omega)]
  have e1 : q + 8 - (q + 4) = 4 := by omega
  rw [e1]
  have e2 : q + 8 + 4 - (q + 12) = 0 := by omega
  rw [e2]
  simp only [Nat.pow_zero, Nat.div_one, Nat.reducePow]

theorem b20_locA (base : Memory) (sp V0 V1 : Nat) (h : 28 ≤ sp) :
    (((base.writeLE (sp - 28) 4 V0).writeLE (sp - 24) 8 V1).readLE (sp - 28) 8) =
      V0 % 4294967296 + 4294967296 * (V1 % 4294967296) := by
  obtain ⟨q, rfl⟩ : ∃ q, sp = q + 28 := ⟨sp - 28, by omega⟩
  have e1 : q + 28 - 28 = q := by omega
  have e2 : q + 28 - 24 = q + 4 := by omega
  rw [e1, e2]
  exact b20_locA0 base q V0 V1

theorem b20_locB (base : Memory) (sp V0 V1 V2 : Nat) (h : 28 ≤ sp) :
    ((((base.writeLE (sp - 28) 4 V0).writeLE (sp - 24) 8 V1).writeLE (sp - 16) 8 V2).readLE (sp - 20) 8) =
      V1 / 4294967296 % 4294967296 + 4294967296 * (V2 % 4294967296) := by
  obtain ⟨q, rfl⟩ : ∃ q, sp = q + 28 := ⟨sp - 28, by omega⟩
  have e1 : q + 28 - 28 = q := by omega
  have e2 : q + 28 - 24 = q + 4 := by omega
  have e3 : q + 28 - 16 = q + 12 := by omega
  have e4 : q + 28 - 20 = q + 8 := by omega
  rw [e1, e2, e3, e4]
  exact b20_locB0 base q V0 V1 V2
end B20

end Fv256.Util
