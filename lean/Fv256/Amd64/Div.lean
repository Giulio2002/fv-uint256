import Extracted
import Fv256.Spec.Div
import Fv256.Amd64.Machine
import Fv256.Proofs.Amd64.Div

/-!
# amd64: the compiled `(*uint256.Int).Div` implements `Spec.div`  (`Fv256/Spec/Div.lean`)

`z.Div(x, y)` (`RAX, RBX, RCX`) returns normally (no fault, no panic, no divide-error trap, also for `y = 0`) with `RAX = z`,
leaves `Spec.div x y` (`x / y`, or `0` when `y = 0`) in `z`, and writes only `z[0, 32)` and its own stack window.
`z`, `x`, `y` may overlap arbitrarily. The proof is `Fv256/Proofs/Amd64/Div.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64

namespace Fv256.Amd64.Div

/-- PRECONDITION (machine facts only). Stack: the stack-growth checks of `Div` and its callee `udivrem` fall through, at least
`0x1c0` bytes of stack exist, and the window `[RSP-0x1b8, RSP+0x10)` (both frames plus the caller's spill slot) is writable.
Buffers: `z` writable, `x`, `y` readable, 32 bytes each (they may alias each other freely), none overlapping the window.
The goroutine's `stackguard0` word at `R14` is outside the window. -/
def Pre (z x y : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0x168 ∧ 0x1c0 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x1b8 0x10 ∧
  Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧
  Outside z 32 ((s.regs regSP).toNat - 0x1b8) ((s.regs regSP).toNat + 0x10) ∧
  Outside x 32 ((s.regs regSP).toNat - 0x1b8) ((s.regs regSP).toNat + 0x10) ∧
  Outside y 32 ((s.regs regSP).toNat - 0x1b8) ((s.regs regSP).toNat + 0x10) ∧
  ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x1b8 ∨ (s.regs regSP).toNat + 0x10 ≤ (s.regs regG).toNat + 16)

/-- POSTCONDITION: `RAX = z`; the number at `z` is `Spec.div` of the numbers at `x` and `y` BEFORE the call; memory changed only
in `z[0, 32)` and the stack window. -/
def Post (z x y : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  valueAt s' z 32 = Fv256.Spec.div (valueAt s x 32) (valueAt s y 32) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x1b8, (s.regs regSP).toNat + 0x10)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y] (Pre z x y) (Post z x y) :=
  correctness_proof z x y

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.Div(x, x)`) satisfies `Pre` and its call returns with `Post`. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧ Pre z x y s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y s s' :=
  Wit.nonvacuous

/-- That concrete call returns `z` holding `0` (the memory it reads is all zero, so this is the `y = 0` case). -/
theorem returns : Returns (Extracted.program.withExit Wit.ret) Wit.s0 fun s' =>
    ABIReturn Wit.s0 s' ∧ s'.regs 0 = Wit.z ∧ valueAt s' Wit.z 32 = 0 :=
  Wit.returns

end Witness

end Fv256.Amd64.Div
