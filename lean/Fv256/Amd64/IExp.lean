import Extracted
import Fv256.Spec.IExp
import Fv256.Proofs.Amd64.IExp

/-!
# amd64: the compiled `(*uint256.Int).IExp` implements `Spec.iExp`  (`Fv256/Spec/IExp.lean`)

`z.IExp(exponent)` (`RAX, RBX`) returns normally (no fault, no panic) with `RAX` = z, leaves `Fv256.Spec.iExp z exponent`
(that is `z ^ exponent mod 2^256`, with `z` the receiver's value before the call) in `z`, and writes only `z[0, 32)` and
its own stack frame. `z` and `exponent` may overlap arbitrarily.
The tactic proof is `Fv256/Proofs/Amd64/IExp.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.IExp

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`StackGuardOK`), enough stack exists, and
the window `[RSP-0xd0, RSP+0x10)` is writable. Data: the binary's read-only data is loaded. Buffers: `z` writable, `x`
(the exponent) readable, 32 bytes each (they may alias), none overlapping the window; the goroutine's `g` words at `R14`
are outside the window. -/
def Pre (z x : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0x48 ∧ 0x128 ≤ (s.regs regSP).toNat ∧ StackWritable s 0xd0 0x10 ∧ Buffer s z 32 true ∧
  Buffer s x 32 false ∧
  (z.toNat + 32 ≤ (s.regs regSP).toNat - 0xd0 ∨ (s.regs regSP).toNat + 0x10 ≤ z.toNat) ∧
  (x.toNat + 32 ≤ (s.regs regSP).toNat - 0xd0 ∨ (s.regs regSP).toNat + 0x10 ≤ x.toNat) ∧
  ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0xd0 ∨ (s.regs regSP).toNat + 0x10 ≤ (s.regs regG).toNat + 16) ∧
  Extracted.program.DataLoaded s.mem

/-- POSTCONDITION: `RAX = z`; the number at `z` is `Spec.iExp` of the numbers at `z` (base) and `x` (exponent) BEFORE the
call; memory changed only in `z[0, 32)` and the callee's stack frame. -/
def Post (z x : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧ valueAt s' z 32 = Fv256.Spec.iExp (valueAt s z 32) (valueAt s x 32) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0xd0, (s.regs regSP).toNat + 0x10)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x] (Pre z x) (Post z x) :=
  correctness_proof z x

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.IExp(x)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧ Pre z x s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.IExp
