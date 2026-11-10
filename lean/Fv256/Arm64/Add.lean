import Extracted
import Fv256.Spec.Add
import Fv256.Arm64.Machine
import Fv256.Proofs.Arm64.Add

/-!
# arm64: the compiled `(*uint256.Int).Add` implements `Spec.add`  (`Fv256/Spec/Add.lean`)

Calling `z.Add(x, y)` with `z, x, y` in `X0, X1, X2` returns normally (no fault, no panic) with `X0 = z`, leaves in `z` the
number `Fv256.Spec.add x y`, and changes no byte outside `z[0, 32)`. `z`, `x`, `y` may coincide but may not partially overlap.
The tactic proof is `Fv256/Proofs/Arm64/Add.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Add

/-- PRECONDITION (machine facts only): `z` is a writable and `x`, `y` are readable 32-byte buffers (`Ptr32`); `z`, `x`, `y` are
pairwise equal-or-disjoint (`Aliasing`, from Janus). -/
def Pre (z x y : BitVec 64) (s : State) : Prop :=
  Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
  Aliasing z x ∧ Aliasing z y ∧ Aliasing x y

/-- POSTCONDITION: `X0 = z`; the number now at `z` is `Spec.add` of the numbers at `x` and `y` BEFORE the call; only `z[0, 32)`
was written. -/
def Post (z x y : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  Janus.Spec.val256 s'.mem z.toNat = Fv256.Spec.add (Janus.Spec.val256 s.mem x.toNat) (Janus.Spec.val256 s.mem y.toNat) ∧
  Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y] (Pre z x y) (Post z x y) :=
  correctness_proof z x y

/-- SPEED: every call meeting `Pre` returns (ABI obeyed, `Post` holding) after executing at most 17 instructions of the model
(`Janus.GoABI.EnsuresWithin`: instructions, not CPU cycles). The code is straight-line, so 17 is the longest and the shortest path
over the aliasing cases. -/
theorem within (z x y : BitVec 64) :
    EnsuresWithin (fun _ => 17) Extracted.program Extracted.entry [z, x, y] (Pre z x y) (Post z x y) :=
  EnsuresWithin.of_ensures (within_proof z x y) (correctness_proof z x y)

/-- SPEED (lower bound): every call meeting `Pre` executes at least 17 instructions before it returns. -/
theorem atLeast (z x y : BitVec 64) :
    RunsAtLeastOnCall (fun _ => 17) Extracted.program Extracted.entry [z, x, y] (Pre z x y) :=
  atLeast_proof z x y

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.Add(x, x)`) satisfies `Pre` and its call returns with `Post`. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧ Pre z x y s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y s s' :=
  Wit.nonvacuous

/-- NON-VACUITY of `within`: the same concrete call (`z.Add(x, x)`) satisfies `Pre` and returns within 17 instructions with `Post`. -/
theorem within : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧ Pre z x y s ∧
    ReturnsWithin 17 (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y s s' :=
  ⟨Wit.ret, Wit.s0, Wit.z, Wit.x, Wit.x, Wit.hret, Wit.setup, Wit.hpre,
    Fv256.Arm64.Add.within Wit.z Wit.x Wit.x Wit.ret Wit.hret Wit.s0 Wit.setup Wit.hpre⟩

/-- NON-VACUITY of `atLeast`: the same call is still running after 17 instructions, and it returns. -/
theorem atLeast : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧ Pre z x y s ∧
    RunsAtLeast 17 (Extracted.program.withExit ret) s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y s s' :=
  ⟨Wit.ret, Wit.s0, Wit.z, Wit.x, Wit.x, Wit.hret, Wit.setup, Wit.hpre,
    Fv256.Arm64.Add.atLeast Wit.z Wit.x Wit.x Wit.ret Wit.hret Wit.s0 Wit.setup Wit.hpre,
    Fv256.Arm64.Add.correctness Wit.z Wit.x Wit.x Wit.ret Wit.hret Wit.s0 Wit.setup Wit.hpre⟩

end Witness

end Fv256.Arm64.Add
