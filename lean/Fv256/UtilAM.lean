import Janus
import Lean

/-! Small arm64 normalisation lemmas for carry chains (`adds/adcs/subs/sbcs` leave `addWithCarry` and
`decide (b ≤ a)` borrows): towards the Nat-level vocabulary of `janus_carry_nf`. -/

namespace Fv256.AM
open Janus Janus.Arm64

theorem awc_fst (a b : BitVec 64) (c : Bool) :
    (addWithCarry a b c).1.toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 64 := by
  simp only [addWithCarry, BitVec.toNat_ofNat]

theorem awc_c (a b : BitVec 64) (c : Bool) :
    (addWithCarry a b c).2.c = decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat) := by
  simp only [addWithCarry, BitVec.toNat_ofNat]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat
  · have : (a.toNat + b.toNat + c.toNat) % 2 ^ 64 ≠ a.toNat + b.toNat + c.toNat := by
      intro he; have := Nat.mod_lt (a.toNat + b.toNat + c.toNat) (Nat.two_pow_pos 64); omega
    simp [this, h]
  · rw [Nat.mod_eq_of_lt (by omega)]; simp [h]

/-- a subtraction borrow as a floor -/
theorem dec_le_div (a b : Nat) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    (decide (b ≤ a)).toNat = (a + 18446744073709551616 - b) / 18446744073709551616 := by
  by_cases h : b ≤ a
  · simp only [h, decide_true, Bool.toNat_true]; omega
  · simp only [h, decide_false, Bool.toNat_false]; omega

/-- an addition carry as a floor -/
theorem dec_add_div (A : Nat) (h : A < 2 * 18446744073709551616) :
    (decide (18446744073709551616 ≤ A)).toNat = A / 18446744073709551616 := by
  by_cases hc : 18446744073709551616 ≤ A
  · simp only [hc, decide_true, Bool.toNat_true]; omega
  · simp only [hc, decide_false, Bool.toNat_false]; omega

/-- `ngc`/`neg` of a carry flag `c ≤ 1` (the `(2^64 - (0 + (2^64-1) + c)) % 2^64` of a borrow turned into a mask) -/
theorem ngc_flag (c : Nat) (hc : c ≤ 1) :
    (18446744073709551616 - (0 % 18446744073709551616 + 18446744073709551615 % 18446744073709551616 + c) % 18446744073709551616) %
      18446744073709551616 = 1 - c := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h <;> subst h <;> decide

theorem flag_mod (c : Nat) (hc : c ≤ 1) :
    (0 % 18446744073709551616 + 0 % 18446744073709551616 + c) % 18446744073709551616 = c := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h <;> subst h <;> decide

theorem small_mod (a : Nat) (h : a < 18446744073709551616) : a % 18446744073709551616 = a := Nat.mod_eq_of_lt h

/-- an `sbcs` limb in the vocabulary of `janus_carry` (carry-in `q = 1 - borrow`): `a + (2^64 - 1 - b) + q = a + (2^64 - b - (1 - q))` -/
theorem sbc_num (a b q : Nat) (hb : b < 18446744073709551616) (hq : q ≤ 1) :
    a + (18446744073709551616 - 1 - b) + q = a + (18446744073709551616 - b - (1 - q)) := by omega

/-- `S % M = E` from `S = E + k M` for `k ≤ 3` (two reductions of the inputs and a final one) -/
theorem mod_cases4 (S E M : Nat) (h : S = E ∨ S = E + M ∨ S = E + 2 * M ∨ S = E + 3 * M) (hE : E < M) : S % M = E := by
  rcases h with h | h | h | h
  · subst h; exact Nat.mod_eq_of_lt hE
  · subst h; rw [Nat.add_comm, Nat.add_mod_left]; exact Nat.mod_eq_of_lt hE
  · subst h; rw [Nat.add_comm, Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hE
  · subst h; rw [Nat.add_comm, Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hE

/-- a negated flag test, for a flag `c ≤ 1`, as an equation (no case split for `omega`) -/
theorem notsub (c : Nat) (hc : c ≤ 1) : (¬ (1 - c = 0)) = (c = 0) := propext (by omega)

theorem notflag (c : Nat) (hc : c ≤ 1) : (¬ (c = 0)) = (c = 1) := propext (by omega)

end Fv256.AM

section
open Lean Elab Tactic Meta
/-- clear every hypothesis (proposition) except the listed ones: a focused context for the side goals of a `simp` discharger -/
elab "keep_only " ids:ident* : tactic => do
  let names := ids.map (·.getId)
  let mut g ← getMainGoal
  let lctx ← g.withContext getLCtx
  let mut ds : Array LocalDecl := #[]
  for d in lctx do ds := ds.push d
  for d in ds.reverse do
    if d.isImplementationDetail then continue
    if names.contains d.userName then continue
    let isP ← g.withContext (isProp d.type)
    if isP then g ← g.tryClear d.fvarId
  replaceMainGoal [g]
end

section
open Lean Elab Tactic Meta
/-- clear the hypotheses about the stack window, the guard word, the receiver pointer and loaded data (not about the
arithmetic of `x`, `y`, `m`), so that `omega` sees only the arithmetic -/
elab "clear_env_facts" : tactic => do
  let mut g ← getMainGoal
  let lctx ← g.withContext getLCtx
  let mut ds : Array LocalDecl := #[]
  for d in lctx do ds := ds.push d
  for d in ds.reverse do
    if d.isImplementationDetail then continue
    let isP ← g.withContext (isProp d.type)
    if !isP then continue
    let s := (← g.withContext (ppExpr d.type)).pretty
    let bad := ["accessible", "s.sp", "S.sp", "regs 28", "regs 30", "DataLoaded", "Extracted"].any (fun b => (s.splitOn b).length > 1)
    if bad then g ← g.tryClear d.fvarId
  replaceMainGoal [g]
end
