import Extracted
import Fv256.Spec.SetBytes
import Fv256.Spec.Util
import Fv256.Proofs.Common.SetBytesBridge
import Fv256.Proofs.Amd64.SetBytes19

/-!
# amd64: the compiled `(*uint256.Int).SetBytes19` implements `Spec.setBytesN 19`  (`Fv256/Spec/SetBytes.lean`)

`z.SetBytes19(in)` takes the receiver `z` in `RAX` and the slice `in = (ptr, len, cap)` in `RBX, RCX, RDI`. When `len ≥ 19` it returns
normally (no fault, no panic) with `RAX = z`, leaves in `z` the big-endian number formed by the first 19 bytes of `in`
(`Fv256.Spec.setBytesN 19`, bytes read before the call), and changes no byte outside `z[0, 32)` and its own stack frame.
When `len < 19` it panics (bounds check) instead (`panics`).
The tactic proof is `Fv256/Proofs/Amd64/SetBytes19.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SetBytes19

/-- PRECONDITION (machine facts only): the slice has at least 19 bytes; the callee's stack frame `[RSP-8, RSP+24)` is writable; `z`
is a writable 32-byte buffer and `in[0, 19)` is readable; `z` and the 19 input bytes do not overlap each other, and neither overlaps the
stack frame. -/
def Pre (z ptr len : BitVec 64) (s : State) : Prop :=
  19 ≤ len.toNat ∧
  StackWritable s 8 24 ∧
  Buffer s z 32 true ∧ Buffer s ptr 19 false ∧
  (z.toNat + 32 ≤ ptr.toNat ∨ ptr.toNat + 19 ≤ z.toNat) ∧
  (z.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
  (ptr.toNat + 19 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ ptr.toNat)

/-- POSTCONDITION: `RAX = z`; the number now at `z` is `Spec.setBytesN 19` of the input bytes `in[i]` (read as they were BEFORE the call,
`s.mem.readLE (ptr + i) 1`); memory changed only in `z[0, 32)` and the stack frame `[RSP-8, RSP+24)`. -/
def Post (z ptr : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  valueAt s' z 32 = Fv256.Spec.setBytesN 19 (fun i => s.mem.readLE (ptr.toNat + i) 1) ∧
  Fv256.Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 8) 32

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, ptr, len, cap] (Pre z ptr len) (Post z ptr) :=
  correctness_proof z ptr len cap

/-- ERROR CASE: with fewer than 19 bytes (`len < 19`) the call hits the bounds check and panics (`runtime.panicBounds`) instead of returning. -/
theorem panics (z ptr len cap : BitVec 64) (hl : len.toNat < 19) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s)
    (hpre : StackWritable s 16 24) (hzb : Buffer s z 32 true) :
    Panics (Extracted.program.withExit ret) s :=
  panics_proof z ptr len cap hl ret hret s hs hpre hzb

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.SetBytes19(in)` on a 19-byte slice) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z ptr len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s ∧ Pre z ptr len s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z ptr s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.SetBytes19
