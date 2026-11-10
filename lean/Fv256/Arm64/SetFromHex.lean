import Extracted
import Fv256.Spec.SetFromHex
import Fv256.Spec.C
import Fv256.Spec.Arm64.SetFromHexLoops
import Fv256.Proofs.Common.HexBridge
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Proofs.Arm64.SetFromHex

/-!
# arm64: the compiled `(*uint256.Int).SetFromHex` implements `Spec.setFromHex`  (`Fv256/Spec/SetFromHex.lean`)

`z.SetFromHex(s)` (`X0`, `X1`, `X2` = `z`, `s.ptr`, `s.len`) returns normally (never faults or panics) and its outcome is exactly
`Fv256.Spec.setFromHex` of the bytes of `s`: on a valid string `err = nil` and `z` holds the number; otherwise `err` is the
package error variable for the reported error (`ErrEmptyString`, ..., `ErrSyntax`). Memory outside `z` and the callee's stack frame is untouched.
The proof is `Fv256/Proofs/Arm64/SetFromHex.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Fv256.C Fv256.Arm64.SetFromHexLoops

namespace Fv256.Arm64.SetFromHex

/-- PRECONDITION (machine facts only): the stack check passes and the frame is usable; `z` is writable and the string `s` readable; the package error variables hold non-nil errors; `z`, `s`, the error table and the stack frame are pairwise disjoint. -/
def Pre (z hp len : BitVec 64) (s : State) : Prop :=
  GuardOK s 48 ∧ StackOK s 72 24 ∧ Ptr32 s.mem z true ∧ Ptr s.mem hp len.toNat false ∧
          Extracted.program.DataLoaded s.mem ∧ s.mem.accessible errBase 96 false = true ∧
          (∀ e, e < 6 → s.mem.readLE (errAddrOf e) 8 ≠ 0) ∧
          Disjoint z.toNat 32 hp.toNat len.toNat ∧ Disjoint z.toNat 32 (s.sp.toNat - 72) 96 ∧
          Disjoint hp.toNat len.toNat (s.sp.toNat - 72) 96 ∧ Disjoint z.toNat 32 errBase 96 ∧
          Disjoint errBase 96 (s.sp.toNat - 72) 96 ∧
          Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 72) 96

/-- POSTCONDITION: `err` (the two result registers) is `nil` when `Spec.setFromHex` yields `ok v` (and `z` is `v`), otherwise the error variable selected by the error (via `HexError.tag`); only `z[0, 32)` and the callee frame were written. -/
def Post (z hp len : BitVec 64) (s s' : State) : Prop :=
  (match Fv256.Spec.setFromHex (Janus.Spec.strBytes s.mem hp.toNat len.toNat) with
   | .ok v =>
      s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ val256 s'.mem z.toNat = v
   | .error e =>
      s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e.tag) 8) ∧
          s'.regs 1 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e.tag + 8) 8)) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat + 16, s.sp.toNat + 24), (s.sp.toNat - 72, s.sp.toNat)]

/-- BRIDGE (not part of the claim): the implementation-shaped postcondition (`parseHex`) is equivalent to `Post`. -/
theorem post_iff (z hp len : BitVec 64) (s s' : State) :
    ((∀ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v →
              s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ val256 s'.mem z.toNat = v) ∧
            (∀ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = .error e →
              s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
              s'.regs 1 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8)) ∧
            MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat + 16, s.sp.toNat + 24), (s.sp.toNat - 72, s.sp.toNat)]) ↔ Post z hp len s s' := by
  unfold Post
  rw [Fv256.HexBridge.parseHex_eq, Fv256.HexBridge.bl_bytesAt]
  generalize Fv256.Spec.setFromHex (Janus.Spec.strBytes s.mem hp.toNat len.toNat) = r
  rw [← and_assoc]
  apply and_congr_left
  intro _
  cases r with
  | ok v => simp [Fv256.HexBridge.toExcept]
  | error e => simp [Fv256.HexBridge.toExcept]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z hp len : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, hp, len]
      (Pre z hp len) (Post z hp len) :=
  (correctness_proof z hp len).mono (fun _ hs => hs) (fun s s' _ hq => (post_iff z hp len s s').1 hq)

namespace Witness

/-- NON-VACUITY: the hypotheses and `Pre` are jointly satisfiable by a concrete call, which returns with `Post`. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z hp len : BitVec 64),
    RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, hp, len] s ∧
    (Pre z hp len s) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z hp len s s' := by
  obtain ⟨ret, s, z, hp, len, c1, c2, c3, hret⟩ := Wit.nonvacuous
  exact ⟨ret, s, z, hp, len, c1, c2, c3, hret.mono fun s' ⟨ha, hq⟩ => ⟨ha, (post_iff z hp len s s').1 hq⟩⟩

end Witness

end Fv256.Arm64.SetFromHex
