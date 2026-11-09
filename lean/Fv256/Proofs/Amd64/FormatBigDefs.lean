import Extracted
import Fv256.Proofs.Common.IntoBigCommon
import Fv256.Proofs.Common.FormatFastDefs
import Fv256.Proofs.Amd64.FM.IntoBigDefs
import Fv256.Spec.Amd64.FormatBigDefs

/-!
# `(*uint256.Int).Format`, big path (iii) (amd64): definitions

The big path starts at `Format+0x1cc` (frame `r = RSP`, `[r+0x50..0x68]` the spills `z, tab, data, ch`, the 8-byte slot at `r+0x28`):
`slot := 0; IntoBig(z, &slot); (*big.Int).Format(slot, tab, data, ch)`; epilogue; return.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall

namespace Fv256.Amd64.FormatBig

open Fv256.Amd64.IntoBig

/-- the extra facts of the big path about the runtime model `R2` and the goroutine (the `IntoBig` call needs them, `IntoBig`'s `Pre`),
at the state `S0` after the prologue (`r = RSP`): the stack guard leaves room for `IntoBig` (4128 bytes below its entry `RSP`), the
write-barrier flag is readable, `g.stackguard0` and `z` and the two type descriptors are outside the runtime's ranges, the model serves
the requests `IntoBig` makes, the allocation budget covers `IntoBig`'s two objects -/
def BigR2 (R2 : RtInv) (b0 : Nat) (z : BitVec 64) (S0 : State) : Prop :=
  S0.mem.readLE ((S0.regs 14).toNat + 16) 8 + 4136 < (S0.regs 4).toNat ∧
  Outside ((S0.regs 14).toNat + 16) 8 R2.rt ∧
  S0.mem.accessible flagAddr 4 false = true ∧ Outside bigType 16 R2.rt ∧ Outside arrType 16 R2.rt ∧
  Outside z.toNat 32 R2.rt ∧
  R2.ok (Extracted.program.contractAddr "runtime.newobject") [bigType] ∧
  R2.ok (Extracted.program.contractAddr "runtime.newobject") [arrType] ∧
  R2.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
  R2.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
  blockSize 32 false + blockSize 32 true ≤ b0

/-- the state-level result of the big path from the `Format+0x1cc` state `S` (frame of `S0`): returned (`RSP` restored, `RBP` restored from
the saved slot), the registers `R14`, `X15` kept, memory changed only in the runtime's ranges, the callee windows, the spill area and
the 8-byte slot, and the `(*big.Int).Format` results satisfy `RBf` -/
def BigQ (R2 : RtInv) (rt : List (Nat × Nat)) (stack : Nat) (RBf : Res) (tab data ch : BitVec 64) (S0 S' : State) : Prop :=
  S'.regs 4 = S0.regs 4 + 80#64 ∧ S'.regs 5 = BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 64) 8) ∧
  S'.regs 14 = S0.regs 14 ∧ S'.xmm 15 = S0.xmm 15 ∧
  MemFrame S0.mem S'.mem (R2.rt ++ Fv256.FormatFast.FL rt (S0.regs 4).toNat stack ++ [((S0.regs 4).toNat + 0x28, (S0.regs 4).toNat + 0x30)]) ∧
  ∃ P j0 j3 j1, RBf (BitVec.ofNat 64 P) tab data (BitVec.ofNat 64 (ch.toNat % 2 ^ 32)) j0 j3 j1

/-- a `big.Int` object (its header block and its word block in `R`) survives an 8-byte store outside `R` -/
theorem bigObj_writeLE {m : Memory} {R : List (Nat × Nat)} {P v a x : Nat} (h : Fv256.IntoBig.BigObj m P v)
    (hPin : InRanges P 32 R) (hAin : InRanges (m.readLE (P + 8) 8) 32 R) (ho : Outside a 8 R) :
    Fv256.IntoBig.BigObj (m.writeLE a 8 x) P v := by
  obtain ⟨ap, len, cap, hacc, h48, h0, h1, h2, h3, h4, hacc2, h48', hlen, hnorm, hv⟩ := h
  obtain ⟨r1, hr1, hp1, hp2⟩ := hPin
  have hd1 := MemFrame.outside_mem ho hr1
  have hAin' := hAin
  rw [h1] at hAin'
  obtain ⟨r2, hr2, ha1, ha2⟩ := hAin'
  have hd2 := MemFrame.outside_mem ho hr2
  have rd : ∀ b n, (b + n ≤ a ∨ a + 8 ≤ b) → (m.writeLE a 8 x).readLE b n = m.readLE b n := fun b n hb =>
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := m) (v := x) (by omega)
  refine ⟨ap, len, cap, ?_, h48, ?_, ?_, ?_, ?_, h4, ?_, h48', hlen, ?_, ?_⟩
  · rw [Janus.Arm64.Memory.accessible_writeLE]; exact hacc
  · rw [rd P 1 (by omega)]; exact h0
  · rw [rd (P + 8) 8 (by omega)]; exact h1
  · rw [rd (P + 16) 8 (by omega)]; exact h2
  · rw [rd (P + 24) 8 (by omega)]; exact h3
  · rw [Janus.Arm64.Memory.accessible_writeLE]; exact hacc2
  · rcases hnorm with hn | hn
    · exact Or.inl hn
    · refine Or.inr ?_
      rw [rd (ap + 8 * (len - 1)) 8 (by omega)]; exact hn
  · rw [← hv]
    refine Fv256.C.bigAbs_congr _ _ _ (fun i hi => ?_)
    rw [rd (ap + 8 * i) 8 (by omega)]

end Fv256.Amd64.FormatBig
