import Extracted
import Fv256.Spec.PutUint256
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Arm64.PutUint256
import Fv256.Proofs.Arm64.PutUint256Bridge

/-!
# arm64: the compiled `(*uint256.Int).PutUint256(dest []byte)` implements `Spec.putUint256`  (`Fv256/Spec/PutUint256.lean`)

`z.PutUint256(dest)` (`z` in `X0`, the slice `dest` = pointer, length, capacity in `X1`, `X2`, `X3`) returns normally (no fault, no
panic) obeying the ABI when `len(dest) ≥ 32`; `dest[0, 32)` then holds `Fv256.Spec.putUint256 x`, the 32-byte big-endian encoding of the
number `x` at `z` (read before the call). SCOPE: a shorter `dest` panics in Go (`_ = dest[31]`) and is excluded by the precondition
`32 ≤ len`. Only `dest[0, 32)` and the callee frame `[SP-24, SP+24)` are written.
The proof is `Fv256/Proofs/Arm64/PutUint256.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Arm64/PutUint256Bridge.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.PutUint256

/-- PRECONDITION: `32 ≤ len(dest)` (the panicking short-slice case is out of scope); the stack-growth check falls through (`GuardOK`) and the frame `[SP-24, SP+24)` is writable and aligned (`StackOK`); `z` addresses 32 readable bytes and `dest` 32 writable bytes; `z`, `dest` and the frame are pairwise disjoint. -/
def Pre (z ptr len : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 24 24 ∧ 32 ≤ len.toNat ∧ Ptr32 s.mem z false ∧ Ptr s.mem ptr 32 true ∧
  Disjoint z.toNat 32 ptr.toNat 32 ∧ Disjoint z.toNat 32 (s.sp.toNat - 24) 48 ∧
  Disjoint ptr.toNat 32 (s.sp.toNat - 24) 48

/-- POSTCONDITION: `dest[0, 32)` holds `Spec.putUint256` of the number at `z` BEFORE the call; no byte outside `dest[0, 32)` and the callee frame changed. -/
def Post (z ptr : BitVec 64) (s s' : State) : Prop :=
  (List.range 32).map (fun i => s'.mem.readLE (ptr.toNat + i) 1) = Fv256.Spec.putUint256 (val256 s.mem z.toNat) ∧
  Util.OnlyWrites2 s.mem s'.mem ptr.toNat 32 (s.sp.toNat - 24) 48

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

end Fv256.Arm64.PutUint256
