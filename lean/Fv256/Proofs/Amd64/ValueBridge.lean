import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.ValueBridge
import Fv256.Spec.Value
import Fv256.Proofs.Amd64.Value

/-!
# amd64: `Value` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
open Fv256.E
open Fv256.Amd64.Dec
open Fv256.Amd64.SbtsG

namespace Fv256.Amd64.Value.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (R : RtInv) (z : BitVec 64) (s s' : State) :
    (s'.regs 0 = Extracted.dataAddr.«type:string#f88732b8» ∧
    (∃ p l, BoxWords' R.rt s'.mem (s'.regs 3).toNat [p, l] ∧ StrOut s'.mem p l (decBytes (valueAt s z 32))) ∧
    s'.regs 1 = 0 ∧ s'.regs 7 = 0 ∧
    MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)])) ↔
    (s'.regs 0 = Extracted.dataAddr.«type:string#f88732b8» ∧
    (∃ p l, BoxWords' R.rt s'.mem (s'.regs 3).toNat [p, l] ∧ StrOut s'.mem p l (Fv256.Spec.value (valueAt s z 32))) ∧
    s'.regs 1 = 0 ∧ s'.regs 7 = 0 ∧
    MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)])) := by
  simp only [Fv256.Proofs.Value.decLen_eq, ← Fv256.Proofs.Value.value_eq]
  try exact Iff.rfl

/-- The precondition as the proof states it is equivalent to the claim's readable form (`Pre`). -/
theorem pre_iff (R : RtInv) (z : BitVec 64) (s : State) :
    (StackGuardOK s 4600 ∧ Outside ((s.regs 14).toNat + 16) 8 R.rt ∧ StackWritable s 4600 8 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - 4600) (4600 + 8) R.rt ∧ Outside 5163273 256 R.rt ∧ Outside 5176582 256 R.rt ∧ Outside 5134938 256 R.rt ∧
    (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
    (z.toNat + 32 ≤ (s.regs 4).toNat - 4600 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
    ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4600 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
    (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
      HL R [0, (s.regs 4).toNat - 32 - 0x178 + 86 + (98 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
        (s.regs 14).toNat ((s.regs 4).toNat - 32 - 0x178 - 8) (rtView R.rt s.mem)) ∧
    (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
      HL R [0, (s.regs 4).toNat - 32 - 384 - 0x20 + (24 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
        (s.regs 14).toNat ((s.regs 4).toNat - 32 - 384 - 0x58) (rtView R.rt s.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
      MemFrame s.mem M (R.rt ++ [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) →
      (s.mem.readLE z.toNat 32 < 100 → MemFrame s.mem M [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) →
      StrOut M p l (decBytes (s.mem.readLE z.toNat 32)) →
      DecAt R.rt 5163273 5176582 5134938 p l →
      (100 ≤ s.mem.readLE z.toNat 32 →
        R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 M) ∧ 16 ≤ b1 ∧ (0 < l → InRanges p l L1)) →
      ∃ (L : List (Nat × Nat)) (b : Nat),
        LiveAt R cvAddr [p, l] L b (convTstringLive.cost [p, l] M) (s.regs 14).toNat M
          (window64 ((s.regs 4).toNat - 32) 4096 2) ∧
        (InRanges p l R.rt → InRanges p l L))) ↔
    (StackGuardOK s 4600 ∧ Outside ((s.regs 14).toNat + 16) 8 R.rt ∧ StackWritable s 4600 8 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - 4600) (4600 + 8) R.rt ∧ Outside 5163273 256 R.rt ∧ Outside 5176582 256 R.rt ∧ Outside 5134938 256 R.rt ∧
    (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
    (z.toNat + 32 ≤ (s.regs 4).toNat - 4600 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
    ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4600 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
    (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
      HL R [0, (s.regs 4).toNat - 32 - 0x178 + 86 + (98 - (Fv256.Spec.value (s.mem.readLE z.toNat 32)).length), (Fv256.Spec.value (s.mem.readLE z.toNat 32)).length]
        (s.regs 14).toNat ((s.regs 4).toNat - 32 - 0x178 - 8) (rtView R.rt s.mem)) ∧
    (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
      HL R [0, (s.regs 4).toNat - 32 - 384 - 0x20 + (24 - (Fv256.Spec.value (s.mem.readLE z.toNat 32)).length), (Fv256.Spec.value (s.mem.readLE z.toNat 32)).length]
        (s.regs 14).toNat ((s.regs 4).toNat - 32 - 384 - 0x58) (rtView R.rt s.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
      MemFrame s.mem M (R.rt ++ [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) →
      (s.mem.readLE z.toNat 32 < 100 → MemFrame s.mem M [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) →
      StrOut M p l (Fv256.Spec.value (s.mem.readLE z.toNat 32)) →
      DecAt R.rt 5163273 5176582 5134938 p l →
      (100 ≤ s.mem.readLE z.toNat 32 →
        R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 M) ∧ 16 ≤ b1 ∧ (0 < l → InRanges p l L1)) →
      ∃ (L : List (Nat × Nat)) (b : Nat),
        LiveAt R cvAddr [p, l] L b (convTstringLive.cost [p, l] M) (s.regs 14).toNat M
          (window64 ((s.regs 4).toNat - 32) 4096 2) ∧
        (InRanges p l R.rt → InRanges p l L))) := by
  simp only [Fv256.Proofs.Value.decLen_eq, ← Fv256.Proofs.Value.value_eq]
  try exact Iff.rfl

end Fv256.Amd64.Value.Bridge
