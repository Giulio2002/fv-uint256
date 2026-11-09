import Extracted
import Fv256.Spec.HashTreeRoot
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Amd64.HashTreeRoot
import Fv256.Proofs.Amd64.HashTreeRootBridge

/-!
# amd64: the compiled `(*uint256.Int).HashTreeRoot() ([32]byte, error)` implements `Spec.hashTreeRoot`  (`Fv256/Spec/HashTreeRoot.lean`)

`z.HashTreeRoot()` (`z` in `RAX`) returns normally (no fault, no panic) obeying the ABI; the 32 result bytes, which the callee leaves in the
caller's frame at `RSP+8`, are `Fv256.Spec.hashTreeRoot x` (the 32-byte LITTLE-endian serialization of the number `x` at `z`, read
before the call), and the returned `error` interface is nil (`RAX = 0`, `RBX = 0`); no byte outside the result bytes and the callee
frame `[RSP-112, RSP+40)` changes.
The proof is `Fv256/Proofs/Amd64/HashTreeRoot.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Amd64/HashTreeRootBridge.lean`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.HashTreeRoot

/-- PRECONDITION (machine facts only): the stack-growth check falls through (`StackGuardOK`); the frame window `[RSP-112, RSP+40)` (callee frame, local array, and the 32 result bytes at `RSP+8`) is writable; `z` addresses 32 readable bytes that do not overlap that window. -/
def Pre (z : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 112 40 ∧ Buffer s z 32 false ∧
  (z.toNat + 32 ≤ (s.regs regSP).toNat - 112 ∨ (s.regs regSP).toNat + 40 ≤ z.toNat)

/-- POSTCONDITION: the 32 bytes at `RSP+8` are `Spec.hashTreeRoot` of the number at `z` BEFORE the call; the returned `error` is nil (both interface words zero); nothing outside the result bytes and the frame window changed. -/
def Post (z : BitVec 64) (s s' : State) : Prop :=
  (List.range 32).map (fun i => s'.mem.readLE ((s.regs regSP).toNat + 8 + i) 1) = Fv256.Spec.hashTreeRoot (valueAt s z 32) ∧
  s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧
  Fv256.Util.OnlyWrites2 s.mem s'.mem ((s.regs regSP).toNat + 8) 32 ((s.regs regSP).toNat - 112) 112

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

end Fv256.Amd64.HashTreeRoot
