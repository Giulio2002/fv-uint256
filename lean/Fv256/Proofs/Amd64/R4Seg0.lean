import Fv256.Proofs.Common.ReduceProg
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Amd64.ReduceSpec
import Fv256.Proofs.Common.SegCompose

/-! `reduce4` (amd64): shared predicates of the generated liveness-based segments (tools/g4seg.py). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec

namespace Fv256.Amd64.R4Seg

/-- registers/flags that stay fixed through the straight-line body (after the prologue) -/
def R4Regs (s S' : State) : Prop :=
  S'.regs 4 = s.regs 4 - 288#64 ∧ S'.regs 5 = s.regs 4 - 8#64 ∧ S'.regs 14 = s.regs 14 ∧ S'.xmm 15 = s.xmm 15 ∧
  S'.df = s.df ∧ S'.mxcsr = s.mxcsr

/-- memory: only the frame below the saved `RBP` slot changes (the extra range is the return slot window); the saved `RBP` stays -/
def R4Mem (s : State) (M : Memory) : Prop :=
  MemFrame s.mem M [((s.regs 4).toNat - 288, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] ∧
  M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat

theorem R4Mem.write {s : State} {M : Memory} (h : R4Mem s M) (a k v : Nat)
    (h1 : (s.regs 4).toNat - 288 ≤ a) (h2 : a + k ≤ (s.regs 4).toNat - 8) : R4Mem s (M.writeLE a k v) :=
  ⟨MemFrame.writeLE h.1 v (r := ((s.regs 4).toNat - 288, (s.regs 4).toNat)) (by simp) h1 (by omega),
   by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h.2⟩

end Fv256.Amd64.R4Seg
