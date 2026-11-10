import Extracted
import Fv256.Spec.MulOverflow
import Fv256.Spec.Util
import Fv256.Arm64.Machine
import Fv256.Proofs.Arm64.MulOverflow

/-!
# arm64: the compiled `(*uint256.Int).MulOverflow` implements `Spec.mul` and `Spec.mulOverflows`  (`Fv256/Spec/MulOverflow.lean`)

`z.MulOverflow(x, y)` (`X0, X1, X2`) returns normally (no fault, no panic) with `X0 = z`, leaves `Spec.mul x y` in `z`, returns
the overflow flag in `X1` (`1` exactly when `Spec.mulOverflows x y`, else `0`), and writes only `z[0, 32)` and its own stack
frame. `z`, `x`, `y` are pairwise equal-or-disjoint. The proof is `Fv256/Proofs/Arm64/MulOverflow.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Fv256.Arm64

namespace Fv256.Arm64.MulOverflow

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`GuardOK`) and a 240-byte frame plus 16
bytes above `SP` are usable (`StackOK`). Buffers: `z` writable, `x`, `y` readable, 32 bytes each, pairwise equal-or-disjoint,
none overlapping the frame `[SP-240, SP+16)`. -/
def Pre (z x y : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 240 16 ∧ Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
  Alias32 z x ∧ Alias32 z y ∧ Alias32 x y ∧
  Janus.Spec.Disjoint z.toNat 32 (s.sp.toNat - 240) 256 ∧ Janus.Spec.Disjoint x.toNat 32 (s.sp.toNat - 240) 256 ∧
  Janus.Spec.Disjoint y.toNat 32 (s.sp.toNat - 240) 256

/-- POSTCONDITION: `X0 = z`; `X1` is the overflow flag `Spec.mulOverflows` of the numbers at `x` and `y` BEFORE the call (as
`1`/`0`); the number at `z` is `Spec.mul` of them; memory changed only in `z[0, 32)` and the frame `[SP-240, SP+16)`. -/
def Post (z x y : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  (s'.regs 1).toNat = (if Fv256.Spec.mulOverflows (val256 s.mem x.toNat) (val256 s.mem y.toNat) then 1 else 0) ∧
  val256 s'.mem z.toNat = Fv256.Spec.mul (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
  Fv256.Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 240) 256

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y] (Pre z x y) (Post z x y) :=
  correctness_proof z x y

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.MulOverflow(x, x)`) satisfies `Pre` and its call returns with `Post`. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧ Pre z x y s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y s s' :=
  Wit.nonvacuous

/-- That concrete call returns `z` holding `0` with flag `0` (the memory it reads is all zero). -/
theorem returns : Returns (Extracted.program.withExit Wit.ret) Wit.s0 fun s' =>
    ABIReturn Wit.s0 s' ∧ s'.regs 0 = Wit.z ∧ (s'.regs 1).toNat = 0 ∧ val256 s'.mem Wit.z.toNat = 0 :=
  Wit.returns

end Witness

end Fv256.Arm64.MulOverflow
