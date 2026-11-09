import Extracted
import Fv256.Spec.PutUint256
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Amd64.PutUint256
import Fv256.Proofs.Amd64.PutUint256Bridge

/-!
# amd64: the compiled `(*uint256.Int).PutUint256(dest []byte)` implements `Spec.putUint256`  (`Fv256/Spec/PutUint256.lean`)

`z.PutUint256(dest)` (`z` in `RAX`, the slice `dest` = pointer, length, capacity in `RBX`, `RCX`, `RDI`) returns normally (no fault, no
panic) obeying the ABI when `len(dest) ≥ 32`; `dest[0, 32)` then holds `Fv256.Spec.putUint256 x`, the 32-byte big-endian encoding of the
number `x` at `z` (read before the call). SCOPE: a shorter `dest` panics in Go (`_ = dest[31]`) and is excluded by the precondition
`32 ≤ len`. Only `dest[0, 32)` and the callee frame `[RSP-8, RSP+24)` are written.
The proof is `Fv256/Proofs/Amd64/PutUint256.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Amd64/PutUint256Bridge.lean`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.PutUint256

/-- PRECONDITION: `32 ≤ len(dest)` (the panicking short-slice case is out of scope); the return-address slot and the frame `[RSP-8, RSP+24)` are writable; `z` addresses 32 readable bytes and `dest` 32 writable bytes; `z` and `dest` are disjoint, and neither overlaps the frame. -/
def Pre (z ptr len : BitVec 64) (s : State) : Prop :=
  32 ≤ len.toNat ∧ StackWritable s 8 24 ∧ Buffer s z 32 false ∧ Buffer s ptr 32 true ∧
  (z.toNat + 32 ≤ ptr.toNat ∨ ptr.toNat + 32 ≤ z.toNat) ∧
  (z.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
  (ptr.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ ptr.toNat)

/-- POSTCONDITION: `dest[0, 32)` holds `Spec.putUint256` of the number at `z` BEFORE the call; no byte outside `dest[0, 32)` and the callee frame changed. -/
def Post (z ptr : BitVec 64) (s s' : State) : Prop :=
  (List.range 32).map (fun i => s'.mem.readLE (ptr.toNat + i) 1) = Fv256.Spec.putUint256 (valueAt s z 32) ∧
  Fv256.Util.OnlyWrites2 s.mem s'.mem ptr.toNat 32 ((s.regs regSP).toNat - 8) 32

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, ptr, len, cap]
      (Pre z ptr len) (Post z ptr) :=
  Ensures.mono (correctness_proof z ptr len cap) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff z ptr s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z ptr len cap : BitVec 64), RetAddr Extracted.program ret ∧ CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s ∧ Pre z ptr len s ∧ Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z ptr s s' := by
  obtain ⟨ret, s, z, ptr, len, cap, h0, h1, h2, hr⟩ := Wit.nonvacuous
  exact ⟨ret, s, z, ptr, len, cap, h0, h1, h2, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff z ptr s s').1 hq.2⟩⟩

end Witness

end Fv256.Amd64.PutUint256
