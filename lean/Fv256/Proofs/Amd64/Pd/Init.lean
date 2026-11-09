import Fv256.Proofs.Common.PrettyProg
import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.UtilE
import Fv256.Proofs.Amd64.P.A
import Fv256.Proofs.Common.UtilB2
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.PdCells
import Fv256.Proofs.Amd64.Pd.Tabs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E Fv256.Amd64.P Fv256.Amd64.Pd

namespace Fv256.Amd64.Pd

/-- Entry of `(*Int).PrettyDec`. -/
def pdE : Nat := segAddr Fv256.PrettyProg.program "github.com/holiman/uint256.(*Int).PrettyDec"
/-- The loop head (`MOVQ AX, 0x128(SP)` after the receiver is copied), `0x153` bytes into the function. -/
def pdH : Nat := pdE + 0x153

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem pd_init (s : State) (hpc : s.rip = BitVec.ofNat 64 pdE) (zp : Nat) (e0 : s.regs 0 = BitVec.ofNat 64 zp)
    (hg : StackGuardOK s 0x100) (hw : StackWritable s 0x300 0x18) (hal : (s.regs 4).toNat % 8 = 0)
    (hd : Fv256.PrettyProg.program.DataLoaded s.mem)
    (hz : zp + 32 ≤ 2 ^ 48 ∧ s.mem.accessible zp 32 false = true)
    (hzd : zp + 32 ≤ (s.regs 4).toNat - 0x300 ∨ (s.regs 4).toNat + 0x18 ≤ zp)
    (hv0 : s.mem.readLE zp 32 ≠ 0) (hx15 : s.xmm 15 = 0) :
    ReachesRet Fv256.PrettyProg.program (BitVec.ofNat 64 pdH) s
      (fun S' => S'.regs 0 = 19#64 ∧ S'.regs 1 = 132#64 ∧
        S'.regs 2 = BitVec.ofNat 64 ((s.regs 4).toNat - 320) ∧ S'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 384) ∧
        S'.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8) ∧ S'.regs 6 = 0#64 ∧
        S'.regs 7 = BitVec.ofNat 64 ((s.regs 4).toNat - 80) ∧ S'.regs 9 = BitVec.ofNat 64 ((s.regs 4).toNat - 48) ∧
        S'.regs 14 = s.regs 14 ∧ S'.xmm 15 = 0 ∧ S'.df = s.df ∧
        MemFrame s.mem S'.mem [((s.regs 4).toNat - 0x180, (s.regs 4).toNat + 0x18)] ∧
        S'.mem.readLE ((s.regs 4).toNat + 16) 1 = (s.regs 3).toNat % 256 ∧
        S'.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧
        S'.mem.readLE ((s.regs 4).toNat - 80) 32 = s.mem.readLE zp 32 ∧
        S'.mem.readLE ((s.regs 4).toNat - 48) 32 = 10 ^ 19 ∧
        (∀ p, p < 133 → S'.mem.readLE ((s.regs 4).toNat - 169 - p) 1 = 48) ∧ TabsOK S'.mem ∧
        S'.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8) := by
  have hc : pdE + 0x400 < 2 ^ 47 := by decide
  obtain ⟨hzn, hza⟩ := hz
  obtain ⟨hwb, hwn, hwa⟩ := hw
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hwb hwn hwa hal
  janus64_data hd [hwa]
  have l0 := Janus.Arm64.Memory.readLE_lt s.mem zp 8
  have l1 := Janus.Arm64.Memory.readLE_lt s.mem (zp + 8) 8
  have l2 := Janus.Arm64.Memory.readLE_lt s.mem (zp + 16) 8
  have l3 := Janus.Arm64.Memory.readLE_lt s.mem (zp + 24) 8
  simp only [Nat.reducePow] at l0 l1 l2 l3
  rw [Util.readLE_32] at hv0
  have hnz : ((BitVec.ofNat 64 (s.mem.readLE (zp + 8) 8) ||| BitVec.ofNat 64 (s.mem.readLE zp 8) |||
      BitVec.ofNat 64 (s.mem.readLE (zp + 16) 8) ||| BitVec.ofNat 64 (s.mem.readLE (zp + 24) 8)).toNat = 0) = False := by
    apply eq_false
    intro h
    rw [BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : s.mem.readLE zp 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 8) 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 16) 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 24) 8 < 2 ^ 64)] at h
    simp only [Nat.or_eq_zero_iff] at h
    omega
  janus64_run [e0, hnz] until [pdH]
  have hx0 : (s.xmm 15).toNat = 0 := by rw [hx15]; rfl
  have hr := (s.regs 4).isLt
  have hr0 : 0x300 ≤ (s.regs 4).toNat := by omega
  refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setRegF]
  · simp [setRegF]
  · simp [setRegF]; rw [Fv256.E.bv_sub_lit _ 320 (by omega)]
  · simp [setRegF]; rw [Fv256.E.bv_sub_lit _ 384 (by omega)]
  · simp [setRegF]; rw [Fv256.E.bv_sub_lit _ 8 (by omega)]
  · simp [setRegF]
  · simp [setRegF]; rw [Fv256.E.bv_sub_lit _ 80 (by omega)]
  · simp [setRegF]; rw [Fv256.E.bv_sub_lit _ 48 (by omega)]
  · simp [setRegF]
  · simp [setRegF, setXmmF]; exact hx15
  · simp [setRegF]
  · dsimp only
    repeat' first
      | exact MemFrame.refl _ _
      | refine MemFrame.writeLE ?_ _ (List.mem_singleton_self _) (by omega) (by omega)
  · dsimp only
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simp
  · dsimp only
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.reducePow]
    have := (s.regs 5).isLt
    omega
  · dsimp only
    rw [Util.readLE_32, Util.readLE_32, show (s.regs 4).toNat - 80 + 8 = (s.regs 4).toNat - 72 by omega,
      show (s.regs 4).toNat - 80 + 16 = (s.regs 4).toNat - 64 by omega, show (s.regs 4).toNat - 80 + 24 = (s.regs 4).toNat - 56 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.reducePow, Nat.add_assoc, Nat.reduceAdd]
    omega
  · dsimp only
    rw [Util.readLE_32, show (s.regs 4).toNat - 48 + 8 = (s.regs 4).toNat - 40 by omega,
      show (s.regs 4).toNat - 48 + 16 = (s.regs 4).toNat - 32 by omega, show (s.regs 4).toNat - 48 + 24 = (s.regs 4).toNat - 24 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_inside, Nat.zero_div, Nat.zero_mod]
  · intro p hp
    dsimp only
    have hzb : ∀ e, e < 16 → 64053151420411946063694043751862251568 / 256 ^ e % 256 ^ 1 = 48 := by decide +kernel
    by_cases c1 : p ≤ 15
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
      exact hzb _ (by omega)
    by_cases c2 : p ≤ 20
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
      exact hzb _ (by omega)
    by_cases c3 : p ≤ 36
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
      exact hzb _ (by omega)
    by_cases c4 : p ≤ 52
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
      exact hzb _ (by omega)
    by_cases c5 : p ≤ 68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
      exact hzb _ (by omega)
    by_cases c6 : p ≤ 84
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
      exact hzb _ (by omega)
    by_cases c7 : p ≤ 100
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
      exact hzb _ (by omega)
    by_cases c8 : p ≤ 116
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
      exact hzb _ (by omega)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
      exact hzb _ (by omega)
  · dsimp only
    refine TabsOK.frame (TabsOK.of_loaded hd) (rs := [((s.regs 4).toNat - 0x180, (s.regs 4).toNat + 0x18)]) ?_ ?_
    · repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (List.mem_singleton_self _) (by omega) (by omega)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega)
  · dsimp only
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
end Fv256.Amd64.Pd
