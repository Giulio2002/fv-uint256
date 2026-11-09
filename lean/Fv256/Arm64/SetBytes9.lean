import Extracted
import Fv256.Spec.SetBytes
import Fv256.Spec.Util
import Fv256.Proofs.Common.SetBytesBridge
import Fv256.Proofs.Arm64.SetBytes9

/-!
# arm64: the compiled `(*uint256.Int).SetBytes9` implements `Spec.setBytesN 9`  (`Fv256/Spec/SetBytes.lean`)

`z.SetBytes9(in)` takes the receiver `z` in `X0` and the slice `in = (ptr, len, cap)` in `X1, X2, X3`. When `len ≥ 9` it returns
normally (no fault, no panic) with `X0 = z`, leaves in `z` the big-endian number formed by the first 9 bytes of `in`
(`Fv256.Spec.setBytesN 9`, bytes read before the call), and changes no byte outside `z[0, 32)` and its own stack frame.
When `len < 9` it panics (bounds check) instead (`panics`).
The tactic proof is `Fv256/Proofs/Arm64/SetBytes9.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SetBytes9

/-- PRECONDITION (machine facts only): the slice has at least 9 bytes; the stack-growth check falls through (`GuardOK`) and
a 24-byte frame plus the 24 bytes above `SP` are usable (`StackOK`); `z` is a writable 32-byte object and `in[0, 9)` is readable;
`z` and the 9 input bytes do not overlap each other, and neither overlaps the frame `[SP-24, SP+24)`. -/
def Pre (z ptr len : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 24 24 ∧ 9 ≤ len.toNat ∧
  Ptr32 s.mem z true ∧ Ptr s.mem ptr 9 false ∧
  Disjoint z.toNat 32 ptr.toNat 9 ∧
  Disjoint z.toNat 32 (s.sp.toNat - 24) 48 ∧
  Disjoint ptr.toNat 9 (s.sp.toNat - 24) 48

/-- POSTCONDITION: `X0 = z`; the number now at `z` is `Spec.setBytesN 9` of the input bytes `in[i]` (read as they were BEFORE the call,
`s.mem.readLE (ptr + i) 1`); memory changed only in `z[0, 32)` and the stack frame `[SP-24, SP+24)`. -/
def Post (z ptr : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  val256 s'.mem z.toNat = Fv256.Spec.setBytesN 9 (fun i => s.mem.readLE (ptr.toNat + i) 1) ∧
  Fv256.Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 24) 48

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, ptr, len, cap] (Pre z ptr len) (Post z ptr) :=
  correctness_proof z ptr len cap

/-- ERROR CASE: with fewer than 9 bytes (`len < 9`) the call hits the bounds check and panics (`runtime.panicBounds`) instead of returning. -/
theorem panics (z ptr len cap : BitVec 64) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s)
    (hg : GuardOK s 0) (hst : StackOK s 24 24) :
    len.toNat < 9 → Ptr32 s.mem z true → Panics (Extracted.program.withExit ret) s :=
  panics_proof z ptr len cap ret hret s hs hg hst

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.SetBytes9(in)` on a 9-byte slice) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z ptr len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s ∧ Pre z ptr len s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z ptr s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Arm64.SetBytes9
