import Fv256.Arm64.ReduceSpec
import Fv256.Arm64.SegCompose
import Fv256.Util

/-!
# `reduce4` (arm64): frame invariants shared by all segment lemmas (after the prologue: `SP' = SP - 160`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.ReduceSpec

namespace Fv256.Arm64.R4Seg

/-- registers that stay fixed through the body (`s` = the entry state) -/
def R4Regs (s S : State) : Prop :=
  S.sp = s.sp - 160#64 ∧ S.regs 29 = s.sp - 168#64 ∧ S.regs 28 = s.regs 28

/-- memory facts that stay true through the body: the spilled `x0` at `sp+8`, the saved `x29`, and the frame -/
def R4Mem (s : State) (M : Memory) : Prop :=
  M.readLE (s.sp.toNat + 8) 8 = (s.regs 0).toNat ∧ M.readLE (s.sp.toNat - 168) 8 = (s.regs 29).toNat ∧
  MemFrame s.mem M [(s.sp.toNat - 168, s.sp.toNat + 16)]

/-- a store of `k` bytes at `a` inside `[sp-160, sp+8)` keeps `R4Mem` -/
theorem R4Mem.write {s : State} {M : Memory} (h : R4Mem s M) (a k v : Nat)
    (h1 : s.sp.toNat - 168 ≤ a) (h2 : a + k ≤ s.sp.toNat + 16)
    (hp : s.sp.toNat - 160 ≤ a ∧ a + k ≤ s.sp.toNat + 8) (hsp : 168 ≤ s.sp.toNat) : R4Mem s (M.writeLE a k v) := by
  obtain ⟨h3, h4, h6⟩ := h
  refine ⟨?_, ?_, h6.writeLE v (r := (s.sp.toNat - 168, s.sp.toNat + 16)) (by simp) h1 h2⟩
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h3
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h4

theorem R4Regs.sp_toNat {s S : State} (h : R4Regs s S) (hsp : 168 ≤ s.sp.toNat) : S.sp.toNat + 160 = s.sp.toNat := by
  rw [h.1]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem bv_eq_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

end Fv256.Arm64.R4Seg
