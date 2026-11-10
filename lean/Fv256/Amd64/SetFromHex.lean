import Extracted
import Fv256.Spec.SetFromHex
import Fv256.Spec.C
import Fv256.Spec.Amd64.SetFromHexLoops
import Fv256.Proofs.Common.HexBridge
import Fv256.Spec.Amd64.CallSites.Live
import Fv256.Proofs.Amd64.SetFromHex

/-!
# amd64: the compiled `(*uint256.Int).SetFromHex` implements `Spec.setFromHex`  (`Fv256/Spec/SetFromHex.lean`)

`z.SetFromHex(s)` (`RAX`, `RBX`, `RCX` = `z`, `s.ptr`, `s.len`) returns normally (never faults or panics) and its outcome is exactly
`Fv256.Spec.setFromHex` of the bytes of `s`: on a valid string `err = nil` and `z` holds the number; otherwise `err` is the
package error variable for the reported error (`ErrEmptyString`, ..., `ErrSyntax`). Memory outside `z` and the callee's stack frame is untouched.
The proof is `Fv256/Proofs/Amd64/SetFromHex.lean`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.C Fv256.Amd64.SetFromHexLoops

namespace Fv256.Amd64.SetFromHex

/-- PRECONDITION (machine facts only): the stack check passes and the frame is usable; `z` is writable and the string `s` readable; the package error variables hold non-nil errors; `z`, `s`, the error table and the stack frame are pairwise disjoint. -/
def Pre (z hp len : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 48 24 ∧ Buffer s z 32 true ∧ Buffer s hp len.toNat false ∧
          Extracted.program.DataLoaded s.mem ∧ s.mem.accessible errBase 96 false = true ∧
          (∀ e, e < 6 → s.mem.readLE (errAddrOf e) 8 ≠ 0) ∧
          (z.toNat + 32 ≤ hp.toNat ∨ hp.toNat + len.toNat ≤ z.toNat) ∧
          (z.toNat + 32 ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat + 24 ≤ z.toNat) ∧
          (hp.toNat + len.toNat ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat + 24 ≤ hp.toNat) ∧
          (z.toNat + 32 ≤ errBase ∨ (errBase + 96) ≤ z.toNat) ∧
          ((errBase + 96) ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat + 24 ≤ errBase)

/-- POSTCONDITION: `err` (the two result registers) is `nil` when `Spec.setFromHex` yields `ok v` (and `z` is `v`), otherwise the error variable selected by the error (via `HexError.tag`); only `z[0, 32)` and the callee frame were written. -/
def Post (z hp len : BitVec 64) (s s' : State) : Prop :=
  (match Fv256.Spec.setFromHex (Janus.Spec.strBytes s.mem hp.toNat len.toNat) with
   | .ok v =>
      s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v
   | .error e =>
      s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e.tag) 8) ∧
          s'.regs 3 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e.tag + 8) 8)) ∧
  Janus.MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs 4).toNat + 16, (s.regs 4).toNat + 24),
          ((s.regs 4).toNat - 48, (s.regs 4).toNat)]

/-- BRIDGE (not part of the claim): the implementation-shaped postcondition (`parseHex`) is equivalent to `Post`. -/
theorem post_iff (z hp len : BitVec 64) (s s' : State) :
    ((∀ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v →
              s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
            (∀ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = .error e →
              s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
              s'.regs 3 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8)) ∧
            Janus.MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs 4).toNat + 16, (s.regs 4).toNat + 24),
              ((s.regs 4).toNat - 48, (s.regs 4).toNat)]) ↔ Post z hp len s s' := by
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

end Fv256.Amd64.SetFromHex
