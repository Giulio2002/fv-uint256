import Extracted
import Fv256.Spec.WriteToArray32
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Arm64.WriteToArray32
import Fv256.Proofs.Arm64.WriteToArray32Bridge

/-!
# arm64: the compiled `(*uint256.Int).WriteToArray32(dest *[32]byte)` implements `Spec.writeToArray32`  (`Fv256/Spec/WriteToArray32.lean`)

`z.WriteToArray32(dest)` (`z`, `dest` in `X0`, `X1`) returns normally (no fault, no panic) obeying the ABI: `*dest` (32 bytes) receives the 32-byte big-endian encoding of the number `x` at `z`, as given by
`Fv256.Spec.writeToArray32` (read before the call); no other byte of memory changes.
The proof is `Fv256/Proofs/Arm64/WriteToArray32.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Arm64/WriteToArray32Bridge.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.WriteToArray32

/-- PRECONDITION (machine facts only): `z` addresses 32 readable bytes and `dest` 32 writable bytes, and the two ranges are disjoint. -/
def Pre (z dest : BitVec 64) (s : State) : Prop :=
  Ptr32 s.mem z false ∧ Ptr32 s.mem dest true ∧ Disjoint z.toNat 32 dest.toNat 32

/-- POSTCONDITION: the 32 bytes at `dest` are `Spec.writeToArray32` of the number at `z` BEFORE the call; no byte outside `dest[0, 32)` changed. -/
def Post (z dest : BitVec 64) (s s' : State) : Prop :=
  (List.range 32).map (fun i => s'.mem.readLE (dest.toNat + i) 1) = Fv256.Spec.writeToArray32 (val256 s.mem z.toNat) ∧
  OnlyWrites s.mem s'.mem dest.toNat 32

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

end Fv256.Arm64.WriteToArray32
