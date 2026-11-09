import Extracted
import Fv256.Spec.SizeSSZ
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Amd64.SizeSSZ
import Fv256.Proofs.Amd64.SizeSSZBridge

/-!
# amd64: the compiled `(*Int).SizeSSZ() int` implements `Spec.sizeSSZ`  (`Fv256/Spec/SizeSSZ.lean`)

`z.SizeSSZ()` returns normally (no fault, no panic) obeying the ABI with `RAX = Fv256.Spec.sizeSSZ = 32`, for every receiver (it is not
read, so there is no memory precondition); it has no stack frame of its own beyond the return address.
The proof is `Fv256/Proofs/Amd64/SizeSSZ.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Amd64/SizeSSZBridge.lean`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SizeSSZ

/-- PRECONDITION (machine facts only): the return-address slot is writable. (The receiver `x` is never dereferenced.) -/
def Pre (s : State) : Prop :=
  StackWritable s 0 8

/-- POSTCONDITION: `RAX` is `Spec.sizeSSZ`, 32. -/
def Post (s s' : State) : Prop :=
  (s'.regs 0).toNat = Fv256.Spec.sizeSSZ

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      Pre Post :=
  Ensures.mono (correctness_proof x) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧ CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧ Pre s ∧ Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post s s' := by
  obtain ⟨ret, s, x, h0, h1, h2, hr⟩ := Wit.nonvacuous
  exact ⟨ret, s, x, h0, h1, h2, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff s s').1 hq.2⟩⟩

end Witness

end Fv256.Amd64.SizeSSZ
