import Fv256.ReduceProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecF
import Fv256.Amd64.ReduceSpec
import Fv256.SegCompose

/-! `reduce4` (amd64): shared predicates of the generated liveness-based segments (tools/g4seg.py). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec

namespace Fv256.Amd64.R4Seg

/-- registers/flags that stay fixed through the straight-line body (after the prologue) -/
def R4Regs (s S' : State) : Prop :=
  S'.regs 4 = s.regs 4 - 288#64 ∧ S'.regs 5 = s.regs 4 - 8#64 ∧ S'.regs 14 = s.regs 14 ∧ S'.xmm 15 = s.xmm 15 ∧
  S'.df = s.df ∧ S'.mxcsr = s.mxcsr

/-- memory: only the frame below the entry stack pointer changes (the extra range is the return slot window) -/
def R4Mem (s : State) (M : Memory) : Prop :=
  MemFrame s.mem M [((s.regs 4).toNat - 288, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)]

theorem R4Mem.write {s : State} {M : Memory} (h : R4Mem s M) (a k v : Nat)
    (h1 : (s.regs 4).toNat - 288 ≤ a) (h2 : a + k ≤ (s.regs 4).toNat) : R4Mem s (M.writeLE a k v) :=
  MemFrame.writeLE h v (r := ((s.regs 4).toNat - 288, (s.regs 4).toNat)) (by simp) h1 h2

end Fv256.Amd64.R4Seg
