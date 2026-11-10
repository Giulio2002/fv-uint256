import Extracted
import Fv256.Spec.SetBytes
import Fv256.Spec.Util
import Fv256.Proofs.Common.SetBytesBridge
import Fv256.Proofs.Amd64.SetBytes6

/-!
# amd64: the compiled `(*uint256.Int).SetBytes6` implements `Spec.setBytesN 6`  (`Fv256/Spec/SetBytes.lean`)

`z.SetBytes6(in)` takes the receiver `z` in `RAX` and the slice `in = (ptr, len, cap)` in `RBX, RCX, RDI`. When `len ≥ 6` it returns
normally (no fault, no panic) with `RAX = z`, leaves in `z` the big-endian number formed by the first 6 bytes of `in`
(`Fv256.Spec.setBytesN 6`, bytes read before the call), and changes no byte outside `z[0, 32)` and its own stack frame.
When `len < 6` it panics (bounds check) instead (`panics`).
The tactic proof is `Fv256/Proofs/Amd64/SetBytes6.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SetBytes6

/-- PRECONDITION (machine facts only): the slice has at least 6 bytes; the callee's stack frame `[RSP-8, RSP+24)` is writable; `z`
is a writable 32-byte buffer and `in[0, 6)` is readable; `z` and the 6 input bytes do not overlap each other, and neither overlaps the
stack frame. -/
def Pre (z ptr len : BitVec 64) (s : State) : Prop :=
  6 ≤ len.toNat ∧
  StackWritable s 8 24 ∧
  Buffer s z 32 true ∧ Buffer s ptr 6 false ∧
  (z.toNat + 32 ≤ ptr.toNat ∨ ptr.toNat + 6 ≤ z.toNat) ∧
  (z.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
  (ptr.toNat + 6 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ ptr.toNat)

/-- POSTCONDITION: `RAX = z`; the number now at `z` is `Spec.setBytesN 6` of the input bytes `in[i]` (read as they were BEFORE the call,
`s.mem.readLE (ptr + i) 1`); memory changed only in `z[0, 32)` and the stack frame `[RSP-8, RSP+24)`. -/
def Post (z ptr : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  valueAt s' z 32 = Fv256.Spec.setBytesN 6 (fun i => s.mem.readLE (ptr.toNat + i) 1) ∧
  Fv256.Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 8) 32

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, ptr, len, cap] (Pre z ptr len) (Post z ptr) :=
  correctness_proof z ptr len cap

/-- ERROR CASE: with fewer than 6 bytes (`len < 6`) the call hits the bounds check and panics (`runtime.panicBounds`) instead of returning. -/
theorem panics (z ptr len cap : BitVec 64) (hl : len.toNat < 6) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s)
    (hpre : StackWritable s 16 24) :
    Panics (Extracted.program.withExit ret) s :=
  panics_proof z ptr len cap hl ret hret s hs hpre

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.SetBytes6(in)` on a 6-byte slice) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z ptr len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s ∧ Pre z ptr len s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z ptr s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.SetBytes6
