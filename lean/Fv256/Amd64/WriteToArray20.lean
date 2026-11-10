import Extracted
import Fv256.Spec.WriteToArray20
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Amd64.WriteToArray20
import Fv256.Proofs.Amd64.WriteToArray20Bridge

/-!
# amd64: the compiled `(*uint256.Int).WriteToArray20(dest *[20]byte)` implements `Spec.writeToArray20`  (`Fv256/Spec/WriteToArray20.lean`)

`z.WriteToArray20(dest)` (`z`, `dest` in `RAX`, `RBX`) returns normally (no fault, no panic) obeying the ABI: `*dest` (20 bytes) receives the LOW 20 bytes of the number `x` at `z`, big-endian, as given by
`Fv256.Spec.writeToArray20` (read before the call); no other byte of memory changes.
The proof is `Fv256/Proofs/Amd64/WriteToArray20.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Amd64/WriteToArray20Bridge.lean`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.WriteToArray20

/-- PRECONDITION (machine facts only): the return-address slot is writable; `z` addresses 32 readable bytes and `dest` 20 writable bytes; the two ranges are disjoint, and `dest` does not overlap the return-address slot. -/
def Pre (z dest : BitVec 64) (s : State) : Prop :=
  StackWritable s 0 8 ∧ Buffer s z 32 false ∧ Buffer s dest 20 true ∧
  (z.toNat + 32 ≤ dest.toNat ∨ dest.toNat + 20 ≤ z.toNat) ∧
  (dest.toNat + 20 ≤ (s.regs regSP).toNat ∨ (s.regs regSP).toNat + 8 ≤ dest.toNat)

/-- POSTCONDITION: the 20 bytes at `dest` are `Spec.writeToArray20` of the number at `z` BEFORE the call; no byte outside `dest[0, 20)` changed. -/
def Post (z dest : BitVec 64) (s s' : State) : Prop :=
  (List.range 20).map (fun i => s'.mem.readLE (dest.toNat + i) 1) = Fv256.Spec.writeToArray20 (valueAt s z 32) ∧
  Janus.Spec.OnlyWrites s.mem s'.mem dest.toNat 20

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z dest : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, dest]
      (Pre z dest) (Post z dest) :=
  Ensures.mono (correctness_proof z dest) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff z dest s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z dest : BitVec 64), RetAddr Extracted.program ret ∧ CallSetup (Extracted.program.withExit ret) Extracted.entry [z, dest] s ∧ Pre z dest s ∧ Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z dest s s' := by
  obtain ⟨ret, s, z, dest, h0, h1, h2, hr⟩ := Wit.nonvacuous
  exact ⟨ret, s, z, dest, h0, h1, h2, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff z dest s s').1 hq.2⟩⟩

end Witness

end Fv256.Amd64.WriteToArray20
