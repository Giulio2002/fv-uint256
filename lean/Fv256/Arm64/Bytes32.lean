import Extracted
import Fv256.Spec.Bytes32
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Arm64.Bytes32
import Fv256.Proofs.Arm64.Bytes32Bridge

/-!
# arm64: the compiled `(*uint256.Int).Bytes32` implements `Spec.bytes32`  (`Fv256/Spec/Bytes32.lean`)

`z.Bytes32()` (`z` in `X0`) returns normally (no fault, no panic) obeying the ABI; the 32 result bytes, which the callee leaves in the
caller's frame at `SP+8`, are `Fv256.Spec.bytes32 x` (the 32-byte big-endian encoding of the number `x` at `z`, read before the
call); no byte outside the result bytes and the callee frame `[SP-56, SP)` changes. The proof is `Fv256/Proofs/Arm64/Bytes32.lean`;
the equivalence of the byte-list form with the proof's number-reading form is `Fv256/Proofs/Arm64/Bytes32Bridge.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Bytes32

/-- PRECONDITION (machine facts only): `z` addresses 32 readable bytes; the stack window `[SP-56, SP+40)` (the 48-byte frame, a local array copy, and the 32 result bytes at `SP+8`) is writable and aligned (`StackOK`); that window does not overlap `z`; the frame pointer is the caller's (`X29 = SP - 8`, the Go arm64 convention). -/
def Pre (z : BitVec 64) (s : State) : Prop :=
  Ptr32 s.mem z false ∧ StackOK s 56 40 ∧ Disjoint z.toNat 32 (s.sp.toNat - 56) 96 ∧ s.regs 29 = s.sp - 8#64

/-- POSTCONDITION: the 32 bytes at `SP+8` are `Spec.bytes32` of the number at `z` BEFORE the call; nothing outside the result bytes and the frame changed. -/
def Post (z : BitVec 64) (s s' : State) : Prop :=
  (List.range 32).map (fun i => s'.mem.readLE (s.sp.toNat + 8 + i) 1) = Fv256.Spec.bytes32 (val256 s.mem z.toNat) ∧
  Util.OnlyWrites2 s.mem s'.mem (s.sp.toNat + 8) 32 (s.sp.toNat - 56) 56

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z]
      (Pre z) (Post z) :=
  Ensures.mono (correctness_proof z) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff z s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z : BitVec 64), RetAddr Extracted.program ret ∧ CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s ∧ Pre z s ∧ Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z s s' := by
  obtain ⟨ret, s, z, h0, h1, h2, hr⟩ := Wit.nonvacuous
  exact ⟨ret, s, z, h0, h1, h2, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff z s s').1 hq.2⟩⟩

end Witness

end Fv256.Arm64.Bytes32
