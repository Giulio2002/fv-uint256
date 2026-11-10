import Extracted
import Fv256.Spec.Add
import Fv256.Amd64.Machine
import Fv256.Proofs.Amd64.Add

/-!
# amd64: the compiled `(*uint256.Int).Add` implements `Spec.add`  (`Fv256/Spec/Add.lean`)

Calling `z.Add(x, y)` with `z, x, y` in `RAX, RBX, RCX` returns normally (no fault, no panic) with `RAX = z`, leaves in
`z` the number `Fv256.Spec.add x y`, and changes no byte outside `z[0, 32)`. `z`, `x`, `y` may coincide but may not partially overlap.
The tactic proof is `Fv256/Proofs/Amd64/Add.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64

namespace Fv256.Amd64.Add

/-- PRECONDITION (machine facts only): the return-address slot is writable; `z` is writable and `x`, `y` readable 32-byte
buffers; `z` does not overlap the return-address slot; `z`, `x`, `y` are pairwise equal-or-disjoint. -/
def Pre (z x y : BitVec 64) (s : State) : Prop :=
  StackWritable s 0 8 ∧
  Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧
  Disjoint z 32 (s.regs regSP) 8 ∧
  Alias32 z x ∧ Alias32 z y ∧ Alias32 x y

/-- POSTCONDITION: `RAX = z`; the number now at `z` is `Spec.add` of the numbers at `x` and `y` BEFORE the call; only
`z[0, 32)` was written. -/
def Post (z x y : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  valueAt s' z 32 = Fv256.Spec.add (valueAt s x 32) (valueAt s y 32) ∧
  Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y] (Pre z x y) (Post z x y) :=
  correctness_proof z x y

/-- SPEED: every call meeting `Pre` returns (ABI obeyed, `Post` holding) after executing at most 17 instructions of the model
(`Janus.Amd64.GoABI.EnsuresWithin`: instructions, not CPU cycles). The code is straight-line, so 17 is the longest and the
shortest path over the aliasing cases. -/
theorem within (z x y : BitVec 64) :
    EnsuresWithin (fun _ => 17) Extracted.program Extracted.entry [z, x, y] (Pre z x y) (Post z x y) :=
  EnsuresWithin.of_ensures (within_proof z x y) (correctness_proof z x y)

/-- SPEED (lower bound): every call meeting `Pre` executes at least 17 instructions before it returns. -/
theorem atLeast (z x y : BitVec 64) :
    RunsAtLeastOnCall (fun _ => 17) Extracted.program Extracted.entry [z, x, y] (Pre z x y) :=
  atLeast_proof z x y

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.Add(x, x)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧ Pre z x y s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y s s' :=
  Wit.nonvacuous

/-- NON-VACUITY of `within`: the same concrete call (`z.Add(x, x)`) satisfies `Pre` and returns within 17 instructions with `Post`. -/
theorem within : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧ Pre z x y s ∧
    ReturnsWithin 17 (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y s s' :=
  ⟨Wit.ret, Wit.s0, Wit.z, Wit.x, Wit.x, Wit.hret, Wit.setup, Wit.hpre,
    Fv256.Amd64.Add.within Wit.z Wit.x Wit.x Wit.ret Wit.hret Wit.s0 Wit.setup Wit.hpre⟩

/-- NON-VACUITY of `atLeast`: the same call is still running after 17 instructions, and it returns. -/
theorem atLeast : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧ Pre z x y s ∧
    RunsAtLeast 17 (Extracted.program.withExit ret) s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y s s' :=
  ⟨Wit.ret, Wit.s0, Wit.z, Wit.x, Wit.x, Wit.hret, Wit.setup, Wit.hpre,
    Fv256.Amd64.Add.atLeast Wit.z Wit.x Wit.x Wit.ret Wit.hret Wit.s0 Wit.setup Wit.hpre,
    Fv256.Amd64.Add.correctness Wit.z Wit.x Wit.x Wit.ret Wit.hret Wit.s0 Wit.setup Wit.hpre⟩

end Witness

end Fv256.Amd64.Add
