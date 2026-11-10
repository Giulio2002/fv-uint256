import Extracted
import Fv256.Spec.Bytes32
import Fv256.Amd64.Machine
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Amd64.Bytes32
import Fv256.Proofs.Amd64.Bytes32Bridge

/-!
# amd64: the compiled `(*uint256.Int).Bytes32` implements `Spec.bytes32`  (`Fv256/Spec/Bytes32.lean`)

`z.Bytes32()` (`z` in `RAX`) returns normally (no fault, no panic) obeying the ABI; the 32 result bytes, which the callee leaves in the
caller's frame at `RSP+8`, are `Fv256.Spec.bytes32 x` (the 32-byte big-endian encoding of the number `x` at `z`, read before the
call); no byte outside the result bytes and the callee frame `[RSP-40, RSP+40)` changes. The proof is
`Fv256/Proofs/Amd64/Bytes32.lean`; the equivalence of the byte-list form with the proof's number-reading form is
`Fv256/Proofs/Amd64/Bytes32Bridge.lean`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Bytes32

/-- PRECONDITION (machine facts only): the return-address slot and the frame window `[RSP-40, RSP+40)` (saved frame pointer, local array copy, and the 32 result bytes at `RSP+8`) are writable; `z` addresses 32 readable bytes that do not overlap that window. -/
def Pre (z : BitVec 64) (s : State) : Prop :=
  StackWritable s 40 40 ∧ Buffer s z 32 false ∧
  Fv256.Amd64.Outside z 32 ((s.regs regSP).toNat - 40) ((s.regs regSP).toNat + 40)

/-- POSTCONDITION: the 32 bytes at `RSP+8` are `Spec.bytes32` of the number at `z` BEFORE the call; nothing outside the result bytes and the frame window `[RSP-40, RSP+40)` changed. -/
def Post (z : BitVec 64) (s s' : State) : Prop :=
  (List.range 32).map (fun i => s'.mem.readLE ((s.regs regSP).toNat + 8 + i) 1) = Fv256.Spec.bytes32 (valueAt s z 32) ∧
  Fv256.Util.OnlyWrites2 s.mem s'.mem ((s.regs regSP).toNat + 8) 32 ((s.regs regSP).toNat - 40) 40

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

end Fv256.Amd64.Bytes32
