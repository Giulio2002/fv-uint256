import Extracted
import Fv256.Spec.IMul
import Fv256.Spec.Util
import Fv256.Arm64.Machine
import Fv256.Proofs.Arm64.IMul

/-!
# arm64: the compiled `(*uint256.Int).IMul` implements `Spec.imul`  (`Fv256/Spec/IMul.lean`)

`z.IMul(x)` (`X0, X1`) returns normally (no fault, no panic) with `X0 = z`, leaves `Spec.imul z x` (the old `z` times `x`
modulo `2^256`) in `z`, and writes only `z[0, 32)` and its own stack frame. `z` and `x` are equal or disjoint.
The proof is `Fv256/Proofs/Arm64/IMul.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Fv256.Arm64

namespace Fv256.Arm64.IMul

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`GuardOK`) and a 56-byte frame is usable
(`StackOK`). Buffers: `z` writable, `x` readable, 32 bytes each, equal-or-disjoint, neither overlapping the frame `[SP-56, SP)`. -/
def Pre (z x : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 56 0 ∧ Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Alias32 z x ∧
  Janus.Spec.Disjoint z.toNat 32 (s.sp.toNat - 56) 56 ∧ Janus.Spec.Disjoint x.toNat 32 (s.sp.toNat - 56) 56

/-- POSTCONDITION: `X0 = z`; the number now at `z` is `Spec.imul` of the numbers at `z` and `x` BEFORE the call; memory changed
only in `z[0, 32)` and the frame `[SP-56, SP)`. -/
def Post (z x : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  val256 s'.mem z.toNat = Fv256.Spec.imul (val256 s.mem z.toNat) (val256 s.mem x.toNat) ∧
  Fv256.Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 56) 56

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x] (Pre z x) (Post z x) :=
  correctness_proof z x

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧ Pre z x s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x s s' :=
  Wit.nonvacuous

/-- The same call, stated directly: it returns `z` holding `Spec.imul` of the old `z` and `x`, writing only the frame. -/
theorem returns : Returns (Extracted.program.withExit Wit.ret) Wit.s0 fun s' =>
    ABIReturn Wit.s0 s' ∧ Post Wit.z Wit.x Wit.s0 s' :=
  Wit.returns

end Witness

end Fv256.Arm64.IMul
