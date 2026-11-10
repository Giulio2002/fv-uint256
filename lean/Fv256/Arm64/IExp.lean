import Extracted
import Fv256.Spec.IExp
import Fv256.Proofs.Arm64.IExp

/-!
# arm64: the compiled `(*uint256.Int).IExp` implements `Spec.iExp`  (`Fv256/Spec/IExp.lean`)

`z.IExp(exponent)` (`X0, X1`) returns normally (no fault, no panic) with `X0` = z, leaves `Fv256.Spec.iExp z exponent`
(that is `z ^ exponent mod 2^256`, with `z` the receiver's value before the call) in `z`, and writes only `z[0, 32)` and
its own stack frame. `z` and `exponent` may overlap arbitrarily.
The tactic proof is `Fv256/Proofs/Arm64/IExp.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.IExp

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`GuardOK`), the frame `[SP-216, SP+8)` is
usable, and the goroutine's `g` words at `X28` are outside it. Data: the binary's read-only data is loaded. Buffers: `z`
writable, `e` (the exponent) readable, 32 bytes each (they may alias), none overlapping the frame. -/
def Pre (z e : BitVec 64) (s : State) : Prop :=
  GuardOK s 80 ∧ StackOK s 216 8 ∧ 384 ≤ s.sp.toNat ∧
  ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 216 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
  Ptr32 s.mem z true ∧ Ptr32 s.mem e false ∧
  Disjoint z.toNat 32 (s.sp.toNat - 216) 208 ∧ Disjoint e.toNat 32 (s.sp.toNat - 216) 208 ∧ Extracted.program.DataLoaded s.mem

/-- POSTCONDITION: `X0 = z`; the number at `z` is `Spec.iExp` of the numbers at `z` (base) and `x` (exponent) BEFORE the call;
memory changed only in `z[0, 32)` and the callee's stack frame. -/
def Post (z e : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  val256 s'.mem z.toNat = Fv256.Spec.iExp (val256 s.mem z.toNat) (val256 s.mem e.toNat) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 216, s.sp.toNat - 8)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z e : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, e] (Pre z e) (Post z e) :=
  correctness_proof z e

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.IExp(x)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z e : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, e] s ∧ Pre z e s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z e s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Arm64.IExp
