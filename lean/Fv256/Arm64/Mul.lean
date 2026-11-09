import Extracted
import Fv256.Spec.Mul
import Fv256.Arm64.Machine
import Fv256.Proofs.Arm64.Mul

/-!
# arm64: the compiled `(*uint256.Int).Mul` implements `Spec.mul`  (`Fv256/Spec/Mul.lean`)

`z.Mul(x, y)` (`X0, X1, X2`) returns normally (no fault, no panic) with `X0 = z`, leaves `Spec.mul x y` (`x * y` modulo
`2^256`) in `z`, and writes only `z[0, 32)` (a leaf function: no stack frame). `z`, `x`, `y` are pairwise equal-or-disjoint.
The proof is `Fv256/Proofs/Arm64/Mul.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Fv256.Arm64

namespace Fv256.Arm64.Mul

/-- PRECONDITION (machine facts only): `z` is a writable and `x`, `y` are readable 32-byte buffers, pairwise equal-or-disjoint. -/
def Pre (z x y : BitVec 64) (s : State) : Prop :=
  Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
  Alias32 z x ∧ Alias32 z y ∧ Alias32 x y

/-- POSTCONDITION: `X0 = z`; the number at `z` is `Spec.mul` of the numbers at `x` and `y` BEFORE the call; only `z[0, 32)` was
written. -/
def Post (z x y : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  val256 s'.mem z.toNat = Fv256.Spec.mul (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
  OnlyWrites s.mem s'.mem z.toNat 32

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y] (Pre z x y) (Post z x y) :=
  correctness_proof z x y

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.Mul(x, x)`) satisfies `Pre` and its call returns with `Post`. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧ Pre z x y s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y s s' :=
  Wit.nonvacuous

/-- That concrete call returns `z` holding `0` (the memory it reads is all zero). -/
theorem returns : Returns (Extracted.program.withExit Wit.ret) Wit.s0 fun s' =>
    ABIReturn Wit.s0 s' ∧ s'.regs 0 = Wit.z ∧ val256 s'.mem Wit.z.toNat = 0 :=
  Wit.returns

end Witness

end Fv256.Arm64.Mul
