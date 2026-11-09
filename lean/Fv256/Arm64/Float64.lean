import Extracted
import Fv256.Spec.Float64
import Fv256.Arm64.Machine
import Fv256.Proofs.Common.Float64Bridge
import Fv256.Proofs.Arm64.Float64

/-!
# arm64: the compiled `(*uint256.Int).Float64` implements `Fv256.Spec.float64Bits`  (`Fv256/Spec/Float64.lean`)

Calling `x.Float64()` with `x` in `X0` returns normally (no fault, no panic) with the 64-bit pattern of the `float64` nearest to the number at `x`
(IEEE 754 round to nearest, ties to even) in the 64-bit register `D0`, and writes only its own stack frame. The floating-point control
register must have its default value `0`.
The tactic proof is `Fv256/Proofs/Arm64/Float64.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Float64

/-- PRECONDITION (machine facts only): `x` is a readable 32-byte buffer (`Ptr32`); the stack-growth check falls through (`GuardOK`) and the 88-byte frame below `SP` is usable
(`StackOK`), not overlapping `x`; the floating-point control register `FPCR` is `0` (round to nearest, default mode). -/
def Pre (x : BitVec 64) (s : State) : Prop :=
  Ptr32 s.mem x false ∧ GuardOK s 0 ∧ StackOK s 88 0 ∧ Disjoint x.toNat 32 (s.sp.toNat - 88) 88 ∧ s.fpcr = 0

/-- POSTCONDITION: `D0` (as 64 bits) is `Spec.float64Bits` of the number at `x` (read BEFORE the call); memory changed only in the frame `[SP-88, SP)`. -/
def Post (x : BitVec 64) (s s' : State) : Prop :=
  s'.getV 0 64 = Fv256.Spec.float64Bits (val256 s.mem x.toNat) ∧
  MemFrame s.mem s'.mem [(s.sp.toNat - 88, s.sp.toNat)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x] (Pre x) (Post x) :=
  (correctness_proof x).mono (fun _ h => h) fun s _ _ h =>
    ⟨h.1.trans (Fv256.Float64Bridge.float64Bits_eq_mem s.mem x.toNat).symm, h.2⟩

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`x.Float64()` on a zero number) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧ Pre x s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post x s s' :=
  by
    obtain ⟨ret, s, x, hr, hc, hp, hret⟩ := Wit.nonvacuous
    exact ⟨ret, s, x, hr, hc, hp, hret.mono fun s' h =>
      ⟨h.1, h.2.1.trans (Fv256.Float64Bridge.float64Bits_eq_mem s.mem x.toNat).symm, h.2.2⟩⟩

end Witness

end Fv256.Arm64.Float64
