import Extracted
import Fv256.Spec.Exp
import Fv256.Proofs.Amd64.Exp

/-!
# amd64: the compiled `(*uint256.Int).Exp` implements `Spec.exp`  (`Fv256/Spec/Exp.lean`)

`z.Exp(base, exponent)` (`RAX, RBX, RCX`) returns normally (no fault, no panic) with `RAX` = z, leaves `Fv256.Spec.exp
base exponent` (that is `base ^ exponent mod 2^256`) in `z`, and writes only `z[0, 32)` and its own stack frame. `z`,
`base`, `exponent` may overlap arbitrarily.
The tactic proof is `Fv256/Proofs/Amd64/Exp.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Exp

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`StackGuardOK`), enough stack exists, and
the window `[RSP-0xa8, RSP+0x20)` is writable. Data: the binary's read-only data is loaded. Buffers: `z` writable, `b`
(base) and `e` (exponent) readable, 32 bytes each (they may alias each other freely), none overlapping the window; the
goroutine's `g` words at `R14` are outside the window. -/
def Pre (z b e : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0x20 ∧ 0x100 ≤ (s.regs regSP).toNat ∧ StackWritable s 0xa8 0x20 ∧ Buffer s z 32 true ∧
  Buffer s b 32 false ∧ Buffer s e 32 false ∧
  (z.toNat + 32 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ z.toNat) ∧
  (b.toNat + 32 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ b.toNat) ∧
  (e.toNat + 32 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ e.toNat) ∧
  ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ (s.regs regG).toNat + 16) ∧
  Extracted.program.DataLoaded s.mem

/-- POSTCONDITION: `RAX = z`; the number at `z` is `Spec.exp` of the numbers at `b` (base) and `e` (exponent) BEFORE the call;
memory changed only in `z[0, 32)` and the callee's stack frame. -/
def Post (z b e : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧ valueAt s' z 32 = Fv256.Spec.exp (valueAt s b 32) (valueAt s e 32) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0xa8, (s.regs regSP).toNat + 0x20)]

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

end Fv256.Amd64.Exp
