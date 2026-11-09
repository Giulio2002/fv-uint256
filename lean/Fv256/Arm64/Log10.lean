import Extracted
import Fv256.Spec.Log10
import Fv256.Proofs.Arm64.Log10

/-!
# arm64: the compiled `(*uint256.Int).Log10` implements `Spec.IsLog10`  (`Fv256/Spec/Log10.lean`)

Go: `func (z *Int) Log10() uint`. Calling it with the receiver `x` returns normally with a result `r` in `X0` that satisfies `Fv256.Spec.IsLog10 x r` (the decimal digit count of `x` minus one; 0 for zero).
No fault and no panic occur. Memory is only read (apart from the callee stack slot).
The tactic proof is `Fv256/Proofs/Arm64/Log10.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Log10

/-- PRECONDITION (machine facts only): the 32 bytes at `x` are readable and do not overlap the callee's stack slot; the Go stack/guard conditions of the call hold; and (runtime contract) the Go globals `uint256.pows64` / `uint256.pows` still hold the powers of ten (`Tabs64`, `TabsBig`) and are not overlapped by the stack slot. -/
def Pre (x : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
    Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32

/-- POSTCONDITION: `X0` is the base-10 logarithm of the number at `x` as specified by `Spec.IsLog10` (`0` for zero, else `r` with `10^r <= x < 10^(r+1)`). -/
def Post (x : BitVec 64) (s s' : State) : Prop :=
  Fv256.Spec.IsLog10 (val256 s.mem x.toNat) (s'.regs 0).toNat

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x] (Pre x) (Post x) :=
  correctness_proof x

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and
`correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧ Pre x s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post x s s' :=
  Wit.nonvacuous

/-- EXACT RESULT on the concrete witness state: the call returns and the result is the expected literal. -/
theorem returns : Returns (Extracted.program.withExit Wit.ret) Wit.s0 fun s' =>
    ABIReturn Wit.s0 s' ∧ (s'.regs 0).toNat = 4 :=
  Wit.returns

end Witness

end Fv256.Arm64.Log10
