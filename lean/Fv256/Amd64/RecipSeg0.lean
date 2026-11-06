import Fv256.Spec
import Fv256.Util
import Fv256.RecipSpec
import Fv256.CodeIn
import Fv256.RecipProg
import Fv256.SegCompose
import Fv256.Amd64.LshNorm
import Fv256.SqrtTac

/-!
# `Reciprocal` (amd64), library summary over `Fv256.RecipProg`: precondition and segment 0 (entry .. the `r0` merge point)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

abbrev recEntry : Nat := segAddr Fv256.RecipProg.program "github.com/holiman/uint256.Reciprocal"

/-- `Reciprocal(m)` called with `m` in `RAX` -/
def RecPre (s : State) : Prop :=
  (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
  0x248 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0x1b8 ∧ StackWritable s 0x240 0x30 ∧ s.xmm 15 = 0 ∧
  Buffer s (s.regs 0) 32 false ∧
  Apart (s.regs 0).toNat 32 ((s.regs 4).toNat - 0x240) 0x270 ∧
  Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 0x240) 0x270

/-- `r0`: the 32-bit first approximation of `2^63 / yh` (`yh` the top 32 bits of the normalised top word) -/
def r0f (y3 : Nat) : Nat := if y3 / 2 ^ 32 = 2 ^ 31 then 2 ^ 32 - 1 else 2 ^ 63 / (y3 / 2 ^ 32)

/-- registers that stay fixed through the body: `RSP` after the prologue, `RBP`, `R14`, `X15` -/
def RecRegs (s S : State) : Prop :=
  S.regs 4 = s.regs 4 - 0x238#64 ∧ S.regs 5 = s.regs 4 - 8#64 ∧ S.regs 14 = s.regs 14 ∧ S.xmm 15 = 0

/-- memory facts that stay true through the body (all later stores go to other scratch slots): the top word `y3` of the normalised copy
`y` of `m` (local at `sp-544`), the spilled `bsr` index at `sp-16`, `y = m << clz`, the frame -/
def RecMem (s : State) (M : Memory) (y3 : Nat) : Prop :=
  y3 = M.readLE ((s.regs 4).toNat - 520) 8 ∧
  M.readLE ((s.regs 4).toNat - 16) 8 = 63 - Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) ∧
  M.readLE ((s.regs 4).toNat - 544) 32 =
    Fv256.Spec.lsh (s.mem.readLE (s.regs 0).toNat 32) (Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8)) ∧
  MemFrame s.mem M [((s.regs 4).toNat - 576, (s.regs 4).toNat + 48)]

/-- a store of `k` bytes at `a`, inside the frame and apart from `y` and the spilled index, keeps `RecMem` -/
theorem RecMem.write {s : State} {M : Memory} {y3 : Nat} (h : RecMem s M y3) (a k v : Nat) (hsp : 576 ≤ (s.regs 4).toNat)
    (h1 : (s.regs 4).toNat - 576 ≤ a) (h2 : a + k ≤ (s.regs 4).toNat + 48)
    (hy : a + k ≤ (s.regs 4).toNat - 544 ∨ (s.regs 4).toNat - 512 ≤ a)
    (hp : a + k ≤ (s.regs 4).toNat - 16 ∨ (s.regs 4).toNat - 8 ≤ a) : RecMem s (M.writeLE a k v) y3 := by
  obtain ⟨h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, h6.writeLE v (r := ((s.regs 4).toNat - 576, (s.regs 4).toNat + 48)) (by simp) h1 h2⟩
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h3
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h4
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h5

/-- the state at `recEntry + 0xe7` (both `yh = 2^31` and not merge here): `RAX = r0`, `RSI = y3` -/
def RecQ0 (s S' : State) : Prop := ∃ y3 : Nat,
  S'.regs 0 = BitVec.ofNat 64 (r0f y3) ∧ S'.regs 6 = BitVec.ofNat 64 y3 ∧
  RecRegs s S' ∧ RecMem s S'.mem y3 ∧ 2 ^ 63 ≤ y3 ∧ y3 < 2 ^ 64

set_option maxRecDepth 100000 in
theorem hcLsh : Janus.Contracts.EqHashModel.CodeIn64 Fv256.LshProg.program Fv256.RecipProg.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem seg0 (s : State) (hpc : s.rip = BitVec.ofNat 64 recEntry) (hpre : RecPre s)
    (hm3 : s.mem.readLE ((s.regs 0).toNat + 24) 8 ≠ 0)
    (hnp : ¬ ((BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) - 1#64 &&&
            BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) |||
          (BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8) |||
              BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 8) 8) |||
            BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 16) 8))).toNat = 0)) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0xe7)) s (RecQ0 s) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hpre
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hsp
  have hclz : s.mem.readLE ((s.regs 0).toNat + 24) 8 ≠ 0 →
      Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) ≤ 63 :=
    fun h => Fv256.Amd64.LshNorm.clz_le _ (Util.readLE8_lt _ _) h
  have hzeq : (s.regs 4 - 0x220#64).toNat = (s.regs 4).toNat - 544 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hz24 : (s.regs 4).toNat - 544 + 24 = (s.regs 4).toNat - 520 := by omega
  janus64_run [Util.readLE_32, hzeq, hz24, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.le_def, BitVec.lt_def,
    BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod]
    until [recEntry + 0xe7]
    calls [hS := Fv256.CodeIn.lib_summary hcLsh (Fv256.Amd64.LshNorm.lsh_norm_summary (s.regs 4 - 0x220#64) (s.regs 0))]
  all_goals (
    have hfr := (show MemFrame _ s'.mem [((s.regs 4).toNat - 544, (s.regs 4).toNat - 544 + 32)] by janus_assumption)
    unfold RecQ0 RecRegs RecMem
    refine ⟨s'.mem.readLE ((s.regs 4).toNat - 520) 8, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ⟨rfl, ?_, ?_, ?_⟩, ?_, ?_⟩
    · first
        | (unfold r0f; rw [if_pos (by omega)]; simp [setRegF])
        | (unfold r0f; rw [if_neg (by omega)]; simp [setRegF])
    · simp [setRegF]
    · dsimp only at *; simp [setRegF] at *; bv_omega
    · dsimp only at *; simp [setRegF] at *; bv_omega
    · dsimp only at *; simp [setRegF] at *; bv_omega
    · dsimp only at *; simp [setRegF] at *; bv_omega
    · rw [hfr.readLE ((s.regs 4).toNat - 16) 8 (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by omega)
    · grab_const Fv256.Spec.lsh as hLvAll
      have hLv := hLvAll.2.2.2.2.2.2.2.1
      simp only [valueAt, hzeq] at hLv ⊢
      simp [setRegF] at hLv
      have hc := hclz hm3
      have hn : (18446744073709551616 - (18446744073709551553 + (63 - Janus.Arm64.clzNat 64 (Janus.Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 0) + 24) 8))) % 18446744073709551616) % 18446744073709551616 = Janus.Arm64.clzNat 64 (Janus.Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 0) + 24) 8) := by omega
      rw [hn] at hLv
      unfold Apart at hdm
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint] at hLv
      exact hLv
    · refine MemFrame.trans (?_ : MemFrame s.mem _ [((s.regs 4).toNat - 576, (s.regs 4).toNat + 48)]) hfr ?_
      · repeat' first
          | exact MemFrame.refl _ _
          | refine MemFrame.writeLE ?_ _ (r := ((s.regs 4).toNat - 576, (s.regs 4).toNat + 48)) (by simp) (by dsimp only; omega) (by dsimp only; omega)
      · intro a n hx
        simp only [Outside, and_true] at hx ⊢
        omega
    · omega
    · omega)

end Fv256.Amd64.RecipSeg
