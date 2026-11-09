import Extracted
import Fv256.Spec.Exp
import Fv256.Proofs.Arm64.Exp

/-!
# arm64: the compiled `(*uint256.Int).Exp` implements `Spec.exp`  (`Fv256/Spec/Exp.lean`)

`z.Exp(base, exponent)` (`X0, X1, X2`) returns normally (no fault, no panic) with `X0` = z, leaves `Fv256.Spec.exp base
exponent` (that is `base ^ exponent mod 2^256`) in `z`, and writes only `z[0, 32)` and its own stack frame. `z`, `base`,
`exponent` may overlap arbitrarily.
The tactic proof is `Fv256/Proofs/Arm64/Exp.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Exp

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`GuardOK`), the frame `[SP-168, SP+40)` is
usable, and the goroutine's `g` words at `X28` are outside it. Data: the binary's read-only data is loaded. Buffers: `z`
writable, `b` (base) and `e` (exponent) readable, 32 bytes each (they may alias each other freely), none overlapping the
frame. -/
def Pre (z b e : BitVec 64) (s : State) : Prop :=
  GuardOK s 32 ∧ StackOK s 168 40 ∧ 336 ≤ s.sp.toNat ∧
  ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 168 ∨ s.sp.toNat + 40 ≤ (s.regs 28).toNat + 16) ∧
  Ptr32 s.mem z true ∧ Ptr32 s.mem b false ∧ Ptr32 s.mem e false ∧
  Disjoint z.toNat 32 (s.sp.toNat - 168) 208 ∧ Disjoint b.toNat 32 (s.sp.toNat - 168) 208 ∧
  Disjoint e.toNat 32 (s.sp.toNat - 168) 208 ∧ Extracted.program.DataLoaded s.mem

/-- POSTCONDITION: `X0 = z`; the number at `z` is `Spec.exp` of the numbers at `b` (base) and `e` (exponent) BEFORE the call;
memory changed only in `z[0, 32)` and the callee's stack frame. -/
def Post (z b e : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  val256 s'.mem z.toNat = Fv256.Spec.exp (val256 s.mem b.toNat) (val256 s.mem e.toNat) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 168, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z b e : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, b, e] (Pre z b e) (Post z b e) :=
  correctness_proof z b e

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.Exp(x, x)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z b e : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, b, e] s ∧ Pre z b e s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z b e s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Arm64.Exp
