import Extracted
import Fv256.Proofs.Common.FormatFastDefsA64

/-!
# `Format` (arm64): the prefix -- prologue to the `z == 0` split, then the two sides

`prefix_nz`: `z ≠ 0`: from the entry to `Format+0x44` (0xb6074, the state `S0` of the fast and big paths), after the `cbnz x0` is taken.
`prefix_z`: `z = 0`: the entry to `Format+0x20` (0xb6050, the `cbnz x0` itself, where FV-N's `nil_path` starts).
The prologue is `ldr x16,[x28,#16]; cmp sp,x16; b.ls morestack; str x30,[sp,#-80]!; stur x29,[sp,#-8]; sub x29,sp,#8;
str x1,[sp,#96]; str x2,[sp,#104]`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.FormatFastA64

namespace Fv256.Arm64.FormatPrefix

set_option linter.janusRenameI false
set_option linter.unusedVariables false

theorem prefix_nz (impl : List Segment) (rt : List (Nat × Nat)) (stack : Nat) (z tab data ch : BitVec 64)
    (s : State) (hpc : s.pc = BitVec.ofNat 64 Extracted.entry)
    (hr0 : s.regs 0 = z) (hr1 : s.regs 1 = tab) (hr2 : s.regs 2 = data) (hr3 : s.regs 3 = ch) (hz : z.toNat ≠ 0)
    (hg : GuardOK s 0)
    (hal : s.sp.toNat % 16 = 0) (hstk : 88 + stack ≤ s.sp.toNat) (hhi : s.sp.toNat + 40 ≤ 2 ^ 48)
    (hacc : s.mem.accessible (s.sp.toNat - 88 - stack) (stack + 128) true = true) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x44)) s
      (fun S0 => S0.regs 0 = z ∧ S0.regs 1 = tab ∧ S0.regs 2 = data ∧ S0.regs 3 = ch ∧ S0.sp = s.sp - 80#64 ∧
        S0.regs 29 = s.sp - 88#64 ∧ S0.regs 28 = s.regs 28 ∧ S0.regs 18 = s.regs 18 ∧
        S0.mem.readLE (s.sp.toNat - 80 + 96) 8 = tab.toNat ∧ S0.mem.readLE (s.sp.toNat - 80 + 104) 8 = data.toNat ∧
        S0.mem.readLE (s.sp.toNat - 80) 8 = (s.regs 30).toNat ∧ S0.mem.readLE (s.sp.toNat - 88) 8 = (s.regs 29).toNat ∧
        MemFrame s.mem S0.mem [(s.sp.toNat - 88, s.sp.toNat - 72), (s.sp.toNat + 16, s.sp.toNat + 32)] ∧
        S0.mem.regions = s.mem.regions) := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  janus_run until [Extracted.entry + 0x44]
  apply ReachesRet.done
  · simp [Extracted.entry]
  have hsp8 : 88 ≤ s.sp.toNat := by omega
  refine ⟨by simp [setReg_apply, hr0], by simp [setReg_apply, hr1], by simp [setReg_apply, hr2], by simp [setReg_apply, hr3],
    rfl, by simp [setReg_apply], by simp [setReg_apply], by simp [setReg_apply], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show s.sp.toNat - 80 + 96 = s.sp.toNat + 16 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have := tab.isLt
    simp only [Nat.reducePow] at this ⊢
    exact Nat.mod_eq_of_lt this
  · rw [show s.sp.toNat - 80 + 104 = s.sp.toNat + 24 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have := data.isLt
    simp only [Nat.reducePow] at this ⊢
    exact Nat.mod_eq_of_lt this
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have := (s.regs 30).isLt
    simp only [Nat.reducePow] at this ⊢
    exact Nat.mod_eq_of_lt this
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have := (s.regs 29).isLt
    simp only [Nat.reducePow] at this ⊢
    exact Nat.mod_eq_of_lt this
  · janus_frame
  · simp only [Janus.Arm64.Memory.regions_writeLE]

theorem prefix_z (impl : List Segment) (rt : List (Nat × Nat)) (stack : Nat) (z tab data ch : BitVec 64)
    (s : State) (hpc : s.pc = BitVec.ofNat 64 Extracted.entry)
    (hr0 : s.regs 0 = z) (hr1 : s.regs 1 = tab) (hr2 : s.regs 2 = data) (hr3 : s.regs 3 = ch) (hz : z.toNat = 0)
    (hg : GuardOK s 0)
    (hal : s.sp.toNat % 16 = 0) (hstk : 88 + stack ≤ s.sp.toNat) (hhi : s.sp.toNat + 40 ≤ 2 ^ 48)
    (hacc : s.mem.accessible (s.sp.toNat - 88 - stack) (stack + 128) true = true) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x20)) s
      (fun S0 => S0.regs 0 = z ∧ S0.regs 1 = tab ∧ S0.regs 2 = data ∧ S0.regs 3 = ch ∧ S0.sp = s.sp - 80#64 ∧
        S0.regs 29 = s.sp - 88#64 ∧ S0.regs 28 = s.regs 28 ∧ S0.regs 18 = s.regs 18 ∧
        S0.mem.readLE (s.sp.toNat - 80 + 96) 8 = tab.toNat ∧ S0.mem.readLE (s.sp.toNat - 80 + 104) 8 = data.toNat ∧
        S0.mem.readLE (s.sp.toNat - 80) 8 = (s.regs 30).toNat ∧ S0.mem.readLE (s.sp.toNat - 88) 8 = (s.regs 29).toNat ∧
        MemFrame s.mem S0.mem [(s.sp.toNat - 88, s.sp.toNat - 72), (s.sp.toNat + 16, s.sp.toNat + 32)] ∧
        S0.mem.regions = s.mem.regions) := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  janus_run [hr0, hz] until [Extracted.entry + 0x20]
  apply ReachesRet.done
  · simp [Extracted.entry]
  have hsp8 : 88 ≤ s.sp.toNat := by omega
  refine ⟨by simp [setReg_apply, hr0], by simp [setReg_apply, hr1], by simp [setReg_apply, hr2], by simp [setReg_apply, hr3],
    rfl, by simp [setReg_apply], by simp [setReg_apply], by simp [setReg_apply], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show s.sp.toNat - 80 + 96 = s.sp.toNat + 16 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have := tab.isLt
    simp only [Nat.reducePow] at this ⊢
    exact Nat.mod_eq_of_lt this
  · rw [show s.sp.toNat - 80 + 104 = s.sp.toNat + 24 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have := data.isLt
    simp only [Nat.reducePow] at this ⊢
    exact Nat.mod_eq_of_lt this
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have := (s.regs 30).isLt
    simp only [Nat.reducePow] at this ⊢
    exact Nat.mod_eq_of_lt this
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have := (s.regs 29).isLt
    simp only [Nat.reducePow] at this ⊢
    exact Nat.mod_eq_of_lt this
  · janus_frame
  · simp only [Janus.Arm64.Memory.regions_writeLE]


end Fv256.Arm64.FormatPrefix
