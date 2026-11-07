import Extracted
import Fv256.FormatFastDefs

/-!
# `Format` (amd64): the prefix -- prologue to the `z == 0` split (`Format+0x20`), then the two sides

`prefix_nz`: `z ≠ 0`: from the entry to `Format+0x45` (the state `S0` of the fast and big paths), establishing `FPre`.
`prefix_z`: `z = 0`: the same, but the target is `Format+0x20` (the `test rax,rax` split, where FV-N's `nil_path` starts). (An earlier attempt stopped nowhere because the `until` list still named `+0x45`.) Note that `janus64_run until [pc]` does not stop at a straight-line fallthrough address (it ran through `Format+0x25` and `Format+0x20` to the `fmt.Fprint` call), only at jump targets: stop the nil prefix at the probe-loop head `Format+0x23e` (jump target of the `jmp` at `+0x40`) or at `Format+0x208` (the `je` target when `s.itab = 0`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFast

namespace Fv256.Amd64.FormatPrefix

set_option maxHeartbeats 4000000 in
theorem prefix_nz (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data ch : BitVec 64)
    (s : State) (hpc : s.rip = BitVec.ofNat 64 Extracted.entry)
    (hr0 : s.regs 0 = z) (hr3 : s.regs 3 = tab) (hr1 : s.regs 1 = data) (hr7 : s.regs 7 = ch) (hz : z.toNat ≠ 0)
    (hg : StackGuardOK s 0)
    (hal : (s.regs 4).toNat % 8 = 0) (hstk : 80 + stack ≤ (s.regs 4).toNat) (hhi : (s.regs 4).toNat + 48 ≤ 2 ^ 48)
    (hacc : s.mem.accessible ((s.regs 4).toNat - 80 - stack) (stack + 0x80) true = true)
    (hout : Outside ((s.regs 4).toNat - 80 - stack) (stack + 0x80) rt) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x45)) s
      (fun S0 => S0.regs 0 = z ∧ S0.regs 3 = tab ∧ S0.regs 1 = data ∧ S0.regs 7 = ch ∧ S0.regs 4 = s.regs 4 - 72#64 ∧
        S0.regs 5 = s.regs 4 - 8#64 ∧ S0.regs 14 = s.regs 14 ∧ S0.xmm = s.xmm ∧ S0.df = s.df ∧ S0.fsBase = s.fsBase ∧
        S0.mem.readLE ((s.regs 4).toNat - 72 + 0x58) 8 = tab.toNat ∧ S0.mem.readLE ((s.regs 4).toNat - 72 + 0x60) 8 = data.toNat ∧
        MemFrame s.mem S0.mem [((s.regs 4).toNat - 80, (s.regs 4).toNat), ((s.regs 4).toNat + 16, (s.regs 4).toNat + 32)] ∧
        S0.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧ S0.mem.regions = s.mem.regions) := by
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2
  janus64_run until [Extracted.entry + 0x45]
  apply ReachesRet.done
  · simp [Extracted.entry]
  refine ⟨by simp [setRegF, hr0], by simp [setRegF, hr3], by simp [setRegF, hr1], by simp [setRegF, hr7],
    by simp [setRegF], by simp [setRegF], by simp [setRegF], rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (s.regs 4).toNat - 72 + 88 = (s.regs 4).toNat + 16 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have := tab.isLt
    simp only [Nat.reducePow] at this ⊢
    exact Nat.mod_eq_of_lt this
  · dsimp only
    rw [show (s.regs 4).toNat - 72 + 96 = (s.regs 4).toNat + 24 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have := data.isLt
    simp only [Nat.reducePow] at this ⊢
    exact Nat.mod_eq_of_lt this
  · janus_frame
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have := (s.regs 5).isLt
    simp only [Nat.reducePow] at this ⊢
    exact Nat.mod_eq_of_lt this
  · simp only [Janus.Arm64.Memory.regions_writeLE]



set_option maxHeartbeats 4000000 in
theorem prefix_z (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data ch : BitVec 64)
    (s : State) (hpc : s.rip = BitVec.ofNat 64 Extracted.entry)
    (hr0 : s.regs 0 = z) (hr3 : s.regs 3 = tab) (hr1 : s.regs 1 = data) (hr7 : s.regs 7 = ch) (hz : z.toNat = 0)
    (hg : StackGuardOK s 0)
    (hal : (s.regs 4).toNat % 8 = 0) (hstk : 80 + stack ≤ (s.regs 4).toNat) (hhi : (s.regs 4).toNat + 48 ≤ 2 ^ 48)
    (hacc : s.mem.accessible ((s.regs 4).toNat - 80 - stack) (stack + 0x80) true = true)
    (hout : Outside ((s.regs 4).toNat - 80 - stack) (stack + 0x80) rt) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x20)) s
      (fun S0 => S0.regs 0 = z ∧ S0.regs 3 = tab ∧ S0.regs 1 = data ∧ S0.regs 7 = ch ∧ S0.regs 4 = s.regs 4 - 72#64 ∧
        S0.regs 5 = s.regs 4 - 8#64 ∧ S0.regs 14 = s.regs 14 ∧ S0.xmm = s.xmm ∧ S0.df = s.df ∧ S0.fsBase = s.fsBase ∧
        S0.mem.readLE ((s.regs 4).toNat - 72 + 0x58) 8 = tab.toNat ∧ S0.mem.readLE ((s.regs 4).toNat - 72 + 0x60) 8 = data.toNat ∧
        MemFrame s.mem S0.mem [((s.regs 4).toNat - 80, (s.regs 4).toNat), ((s.regs 4).toNat + 16, (s.regs 4).toNat + 32)] ∧
        S0.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧ S0.mem.regions = s.mem.regions) := by
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2
  janus64_run until [Extracted.entry + 0x20]
  apply ReachesRet.done
  · simp [Extracted.entry]
  refine ⟨by simp [setRegF, hr0], by simp [setRegF, hr3], by simp [setRegF, hr1], by simp [setRegF, hr7],
    by simp [setRegF], by simp [setRegF], by simp [setRegF], rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (s.regs 4).toNat - 72 + 88 = (s.regs 4).toNat + 16 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have := tab.isLt
    simp only [Nat.reducePow] at this ⊢
    exact Nat.mod_eq_of_lt this
  · dsimp only
    rw [show (s.regs 4).toNat - 72 + 96 = (s.regs 4).toNat + 24 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have := data.isLt
    simp only [Nat.reducePow] at this ⊢
    exact Nat.mod_eq_of_lt this
  · janus_frame
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have := (s.regs 5).isLt
    simp only [Nat.reducePow] at this ⊢
    exact Nat.mod_eq_of_lt this
  · simp only [Janus.Arm64.Memory.regions_writeLE]



end Fv256.Amd64.FormatPrefix
