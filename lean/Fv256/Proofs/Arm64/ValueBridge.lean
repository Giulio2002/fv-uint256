import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.ValueBridge
import Fv256.Spec.Value
import Fv256.Proofs.Arm64.Value

/-!
# arm64: `Value` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts
open Fv256.E
open Fv256.Arm64.Dec
open Fv256.Arm64.CallSites

namespace Fv256.Arm64.Value.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (R : RtInv) (z : BitVec 64) (s s' : State) :
    (s'.regs 0 = Extracted.dataAddr.«type:string#f88732b8» ∧
    (∃ p l, BoxWords' R.rt s'.mem (s'.regs 1).toNat [p, l] ∧ StrOut s'.mem p l (decBytes (val256 s.mem z.toNat))) ∧
    s'.regs 2 = 0 ∧ s'.regs 3 = 0 ∧
    MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4640, s.sp.toNat + 8)])) ↔
    (s'.regs 0 = Extracted.dataAddr.«type:string#f88732b8» ∧
    (∃ p l, BoxWords' R.rt s'.mem (s'.regs 1).toNat [p, l] ∧ StrOut s'.mem p l (Fv256.Spec.value (val256 s.mem z.toNat))) ∧
    s'.regs 2 = 0 ∧ s'.regs 3 = 0 ∧
    MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4640, s.sp.toNat + 8)])) := by
  simp only [Fv256.Proofs.Value.decLen_eq, ← Fv256.Proofs.Value.value_eq]
  try exact Iff.rfl

/-- The precondition as the proof states it is equivalent to the claim's readable form (`Pre`). -/
theorem pre_iff (R : RtInv) (z : BitVec 64) (s : State) :
    (GuardOK s 4608 ∧ Outside ((s.regs 28).toNat + 16) 8 R.rt ∧ StackOK s 4640 8 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4640) (4640 + 8) R.rt ∧ Outside 989280 256 R.rt ∧ Outside 1002589 256 R.rt ∧ Outside 960826 256 R.rt ∧
    Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4640 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
    ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4640 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
    (2 ^ 64 ≤ val256 s.mem z.toNat →
      HL R [0, s.sp.toNat - 32 - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
        (s.regs 28).toNat (s.sp.toNat - 32 - 384) (rtView R.rt s.mem)) ∧
    (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
      HL R [0, s.sp.toNat - 32 - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
        (s.regs 28).toNat (s.sp.toNat - 32 - 384 - 96) (rtView R.rt s.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
      MemFrame s.mem M (R.rt ++ [(s.sp.toNat - 4640, s.sp.toNat + 8)]) →
      (val256 s.mem z.toNat < 100 → MemFrame s.mem M [(s.sp.toNat - 4640, s.sp.toNat + 8)]) →
      StrOut M p l (decBytes (val256 s.mem z.toNat)) →
      DecAt R.rt 989280 1002589 960826 p l →
      (100 ≤ val256 s.mem z.toNat →
        R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 M) ∧ 16 ≤ b1 ∧ (0 < l → InRanges p l L1)) →
      ∃ (L : List (Nat × Nat)) (b : Nat),
        LiveAt R cvAddr [p, l] L b (convTstringLive.cost [p, l] M) (s.regs 28).toNat M
          [(s.sp.toNat - 32 - 4096, s.sp.toNat - 32 - 8), (s.sp.toNat - 32 + 8, s.sp.toNat - 32 + 8 + 8 * 2)] ∧
        (InRanges p l R.rt → InRanges p l L))) ↔
    (GuardOK s 4608 ∧ Outside ((s.regs 28).toNat + 16) 8 R.rt ∧ StackOK s 4640 8 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4640) (4640 + 8) R.rt ∧ Outside 989280 256 R.rt ∧ Outside 1002589 256 R.rt ∧ Outside 960826 256 R.rt ∧
    Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4640 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
    ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4640 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
    (2 ^ 64 ≤ val256 s.mem z.toNat →
      HL R [0, s.sp.toNat - 32 - 384 + 94 + (98 - (Fv256.Spec.value (val256 s.mem z.toNat)).length), (Fv256.Spec.value (val256 s.mem z.toNat)).length]
        (s.regs 28).toNat (s.sp.toNat - 32 - 384) (rtView R.rt s.mem)) ∧
    (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
      HL R [0, s.sp.toNat - 32 - 384 - 32 + (24 - (Fv256.Spec.value (val256 s.mem z.toNat)).length), (Fv256.Spec.value (val256 s.mem z.toNat)).length]
        (s.regs 28).toNat (s.sp.toNat - 32 - 384 - 96) (rtView R.rt s.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
      MemFrame s.mem M (R.rt ++ [(s.sp.toNat - 4640, s.sp.toNat + 8)]) →
      (val256 s.mem z.toNat < 100 → MemFrame s.mem M [(s.sp.toNat - 4640, s.sp.toNat + 8)]) →
      StrOut M p l (Fv256.Spec.value (val256 s.mem z.toNat)) →
      DecAt R.rt 989280 1002589 960826 p l →
      (100 ≤ val256 s.mem z.toNat →
        R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 M) ∧ 16 ≤ b1 ∧ (0 < l → InRanges p l L1)) →
      ∃ (L : List (Nat × Nat)) (b : Nat),
        LiveAt R cvAddr [p, l] L b (convTstringLive.cost [p, l] M) (s.regs 28).toNat M
          [(s.sp.toNat - 32 - 4096, s.sp.toNat - 32 - 8), (s.sp.toNat - 32 + 8, s.sp.toNat - 32 + 8 + 8 * 2)] ∧
        (InRanges p l R.rt → InRanges p l L))) := by
  simp only [Fv256.Proofs.Value.decLen_eq, ← Fv256.Proofs.Value.value_eq]
  try exact Iff.rfl

end Fv256.Arm64.Value.Bridge
