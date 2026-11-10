import Extracted
import Fv256.Spec.SetBytes
import Fv256.Spec.Util
import Fv256.Proofs.Common.SetBytesBridge
import Fv256.Proofs.Arm64.SetBytes

/-!
# arm64: the compiled `(*uint256.Int).SetBytes` implements `Spec.setBytes`  (`Fv256/Spec/SetBytes.lean`)

`z.SetBytes(buf)` takes the receiver `z` in `X0` and the slice `buf = (ptr, len, cap)` in `X1, X2, X3`. For every length it returns
normally (no fault, no panic) with `X0 = z`, leaves in `z` the big-endian number formed by the last `min(len, 32)` bytes of `buf`
(`Fv256.Spec.setBytes`, bytes read before the call), and changes no byte outside `z[0, 32)` and its own stack frame.
The tactic proof is `Fv256/Proofs/Arm64/SetBytes.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SetBytes

/-- PRECONDITION (machine facts only). Slice: `len ≤ cap < 2^48`. Stack: the stack-growth check falls through (`GuardOK`), a 88-byte
frame plus the 72 bytes above `SP` are usable and aligned (`StackOK`), the jump-table data is loaded, and the goroutine's `stackguard0`
word (at `X28 + 16`) is outside the frame. Buffers: `z` is a writable 32-byte object, the `len` bytes of `buf` are readable; `z`, the USED
bytes (the last `usedLen len`, ending at `ptr + len`) and the frame `[SP-88, SP+72)` are pairwise disjoint (the unused leading bytes may
overlap anything). -/
def Pre (z ptr len cap : BitVec 64) (s : State) : Prop :=
  GuardOK s 48 ∧ StackOK s 88 72 ∧ Extracted.program.DataLoaded s.mem ∧
  len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 48 ∧
  Ptr32 s.mem z true ∧ Ptr s.mem ptr len.toNat false ∧
  Disjoint z.toNat 32 (ptr.toNat + len.toNat - Fv256.Spec.usedLen len.toNat) (Fv256.Spec.usedLen len.toNat) ∧
  Disjoint z.toNat 32 (s.sp.toNat - 88) 160 ∧
  Disjoint (ptr.toNat + len.toNat - Fv256.Spec.usedLen len.toNat) (Fv256.Spec.usedLen len.toNat) (s.sp.toNat - 88) 160 ∧
  Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 88) 160

/-- POSTCONDITION: `X0 = z`; the number now at `z` is `Spec.setBytes` of the buffer bytes `buf[i]` (read as they were BEFORE the call,
`s.mem.readLE (ptr + i) 1`) and its length; memory changed only in `z[0, 32)` and the stack frame `[SP-88, SP+72)`. -/
def Post (z ptr len : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  val256 s'.mem z.toNat = Fv256.Spec.setBytes (fun i => s.mem.readLE (ptr.toNat + i) 1) len.toNat ∧
  Fv256.Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 88) 160

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. The tactic proof is stated with the
implementation-shaped `Spec.fromBE`; `Spec.setBytes` is shown equal to it (`Proofs/Common/SetBytesBridge.lean`). -/
theorem correctness (z ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, ptr, len, cap] (Pre z ptr len cap) (Post z ptr len) :=
  (correctness_proof z ptr len cap).mono (fun _ h => h) fun s _ _ h =>
    ⟨h.1, h.2.1.trans (Fv256.Proofs.SetBytes.setBytes_eq_fromBE (fun a => s.mem.readLE a 1) ptr.toNat len.toNat).symm, h.2.2⟩

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.SetBytes(buf)` on a 10-byte buffer) satisfies `Pre` and its call returns with `Post`, so
`Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z ptr len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s ∧ Pre z ptr len cap s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z ptr len s s' := by
  obtain ⟨ret, s, z, ptr, len, cap, hret, hsetup, hpre, hrun⟩ := Wit.nonvacuous
  refine ⟨ret, s, z, ptr, len, cap, hret, hsetup, hpre, hrun.mono ?_⟩
  intro s' h
  exact ⟨h.1, h.2.1, h.2.2.1.trans (Fv256.Proofs.SetBytes.setBytes_eq_fromBE (fun a => s.mem.readLE a 1) ptr.toNat len.toNat).symm, h.2.2.2⟩

end Witness

end Fv256.Arm64.SetBytes
