import Extracted
import Fv256.Spec.MulModWithReciprocal
import Fv256.Proofs.Arm64.MulModWithReciprocal

/-!
# arm64: the compiled `(*uint256.Int).MulModWithReciprocal` implements `Spec.mulModWithReciprocal`  (`Fv256/Spec/MulModWithReciprocal.lean`)

`z.MulModWithReciprocal(x, y, m, mu)` (`X0, X1, X2, X3, X4`) returns normally (no fault, no panic) with `X0` = z, leaves
`Fv256.Spec.mulModWithReciprocal x y m` (that is `(x * y) mod m`, or `0` for `m = 0`) in `z`, and writes only `z[0, 32)`
and its own stack frame, PROVIDED `mu` is a valid reciprocal of `m` (`Fv256.Spec.muOk`, a runtime-contract hypothesis of
the Go API). `z`, `x`, `y`, `m` may overlap arbitrarily.
The tactic proof is `Fv256/Proofs/Arm64/MulModWithReciprocal.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.MulModWithReciprocal

/-- PRECONDITION (machine facts only, plus one runtime contract). Stack: the stack-growth check falls through (`GuardOK`),
`SP` is 16-byte aligned and the 808 bytes from `SP-760` are accessible for writing. Buffers: `z` writable, `x`, `y`, `m`
readable 32-byte buffers and `mu` a readable 40-byte buffer (the 5-word reciprocal), none overlapping the frame (`Apart`);
the goroutine's `g` word at `X28+16` is outside it. Runtime contract (Go API): `Fv256.Spec.muOk` says `mu` is a valid
reciprocal of `m`. -/
def Pre (z x y m mu : BitVec 64) (s : State) : Prop :=
  GuardOK s 720 ∧ s.sp.toNat % 16 = 0 ∧ 760 ≤ s.sp.toNat ∧ s.sp.toNat + 48 ≤ 2 ^ 48 ∧
  s.mem.accessible (s.sp.toNat - 760) (760 + 48) true = true ∧
  Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 760) 808 ∧
  Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Ptr32 s.mem m false ∧ (mu.toNat + 40 ≤ 2 ^ 48 ∧ s.mem.accessible mu.toNat 40 false = true) ∧
  Apart z.toNat 32 (s.sp.toNat - 760) 808 ∧ Apart x.toNat 32 (s.sp.toNat - 760) 808 ∧
  Apart y.toNat 32 (s.sp.toNat - 760) 808 ∧ Apart m.toNat 32 (s.sp.toNat - 760) 808 ∧
  Apart mu.toNat 40 (s.sp.toNat - 760) 808 ∧
  Fv256.Spec.muOk (val256 s.mem m.toNat) (s.mem.readLE mu.toNat 40)

/-- POSTCONDITION: `X0 = z`; the number at `z` is `Spec.mulModWithReciprocal` of the numbers at `x`, `y`, `m` BEFORE the call;
memory changed only in `z[0, 32)` and the callee's stack frame. -/
def Post (z x y m mu : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  val256 s'.mem z.toNat = Fv256.Spec.mulModWithReciprocal (val256 s.mem x.toNat) (val256 s.mem y.toNat) (val256 s.mem m.toNat) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 760, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 48)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x y m mu : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, m, mu] (Pre z x y m mu) (Post z x y m mu) :=
  correctness_proof z x y m mu

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.MulModWithReciprocal(x, y, m, mu)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y m mu : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y, m, mu] s ∧ Pre z x y m mu s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y m mu s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Arm64.MulModWithReciprocal
