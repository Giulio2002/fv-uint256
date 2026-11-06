import Fv256.Arm64.PrettyProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.PdCells
import Fv256.Arm64.P.T
import Fv256.Arm64.P.A
import Fv256.UtilB2
import Fv256.Util
import Fv256.Arm64.Pd.Tabs

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec
open Fv256.E Fv256.Arm64.P Fv256.Arm64.Pd

namespace Fv256.Arm64.Pd

/-- Entry of `(*Int).PrettyDec` (arm64). -/
def pdE : Nat := segAddr Fv256.Arm64.PrettyProg.program "github.com/holiman/uint256.(*Int).PrettyDec"
/-- The loop head (`STR R0, 312(RSP)` after the receiver is copied), `0xfc` bytes into the function. -/
def pdH : Nat := pdE + 0xfc

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem pd_init (s : State) (hpc : s.pc = BitVec.ofNat 64 pdE) (zp : Nat) (e0 : s.regs 0 = BitVec.ofNat 64 zp)
    (hg : GuardOK s 272) (hal : s.sp.toNat % 16 = 0) (h408 : 0x300 ≤ s.sp.toNat) (hsp2 : s.sp.toNat < 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 0x300) (0x300 + 0x18) true = true)
    (hd : Fv256.Arm64.PrettyProg.program.DataLoaded s.mem)
    (hz : zp + 32 ≤ 2 ^ 48 ∧ s.mem.accessible zp 32 false = true)
    (hzd : zp + 32 ≤ s.sp.toNat - 0x300 ∨ s.sp.toNat + 0x18 ≤ zp)
    (hret : (s.regs 30).toNat < 2 ^ 48)
    (hv0 : s.mem.readLE zp 32 ≠ 0) :
    ReachesRet Fv256.Arm64.PrettyProg.program (BitVec.ofNat 64 pdH) s
      (fun S' => S'.regs 0 = 19#64 ∧ S'.regs 2 = 132#64 ∧ S'.regs 3 = BitVec.ofNat 64 (s.sp.toNat - 80) ∧ S'.regs 4 = 0#64 ∧
        S'.regs 6 = BitVec.ofNat 64 (s.sp.toNat - 48) ∧ S'.regs 8 = BitVec.ofNat 64 (s.sp.toNat - 320) ∧
        S'.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 408) ∧ S'.sp = BitVec.ofNat 64 (s.sp.toNat - 400) ∧
        (∀ k, k ∉ [0, 2, 3, 4, 6, 8, 9, 10, 11, 16, 17, 20, 25, 29] → S'.regs k = s.regs k) ∧
        MemFrame s.mem S'.mem [(s.sp.toNat - 408, s.sp.toNat + 0x18)] ∧
        S'.mem.readLE (s.sp.toNat + 16) 1 = (s.regs 1).toNat % 256 ∧
        Fv256.B.wv S'.mem (s.sp.toNat - 80) 4 = Fv256.B.wv s.mem zp 4 ∧
        Fv256.B.wv S'.mem (s.sp.toNat - 48) 4 = 10 ^ 19 ∧
        (∀ p, p < 133 → S'.mem.readLE (s.sp.toNat - 169 - p) 1 = 48) ∧ TabsOK S'.mem ∧
        S'.mem.readLE (s.sp.toNat - 408) 8 = (s.regs 29).toNat ∧ S'.mem.readLE (s.sp.toNat - 400) 8 = (s.regs 30).toNat) := by
  have hc : pdE + 0x400 < 2 ^ 47 := by decide
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hzn, hza⟩ := hz
  janus_data hd [hw]
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
  janus_run [e0, hnz, Nat.or_eq_zero_iff] until [pdH]
  have hr := s.sp.isLt
  have hzb : ∀ e, e < 16 → 64053151420411946063694043751862251568 / 256 ^ e % 256 ^ 1 = 48 := by decide +kernel
  have hzb8 : ∀ e, e < 8 → 3472328296227680304 / 256 ^ e % 256 ^ 1 = 48 := by decide +kernel
  refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setReg]
  · simp [setReg]
  · simp [setReg]; exact Fv256.E.bv_sub_lit _ 80 (by omega)
  · simp [setReg]
  · simp [setReg]; exact Fv256.E.bv_sub_lit _ 48 (by omega)
  · simp [setReg]; exact Fv256.E.bv_sub_lit _ 320 (by omega)
  · simp [setReg]; exact Fv256.E.bv_sub_lit _ 408 (by omega)
  · simp; exact Fv256.E.bv_sub_lit _ 400 (by omega)
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setReg, hk]
  · dsimp only
    repeat' first
      | exact MemFrame.refl _ _
      | refine MemFrame.writeLE ?_ _ (List.mem_singleton_self _) (by omega) (by omega)
  · dsimp only
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  · dsimp only
    rw [Fv256.B.wv4_eq, Fv256.B.wv4_eq, Util.readLE_32, Util.readLE_32, show s.sp.toNat - 80 + 8 = s.sp.toNat - 72 by omega,
      show s.sp.toNat - 80 + 16 = s.sp.toNat - 64 by omega, show s.sp.toNat - 80 + 24 = s.sp.toNat - 56 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.reducePow, Nat.add_assoc, Nat.reduceAdd]
    omega
  · dsimp only
    rw [Fv256.B.wv4_eq, Util.readLE_32, show s.sp.toNat - 48 + 8 = s.sp.toNat - 40 by omega,
      show s.sp.toNat - 48 + 16 = s.sp.toNat - 32 by omega, show s.sp.toNat - 48 + 24 = s.sp.toNat - 24 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    all_goals (try simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv])
    all_goals omega
  · intro p hp
    dsimp only
    by_cases c1 : p ≤ 7
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
      exact hzb8 _ (by omega)
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
    refine TabsOK.frame (TabsOK.of_loaded hd) (rs := [(s.sp.toNat - 408, s.sp.toNat + 0x18)]) ?_ ?_
    · repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (List.mem_singleton_self _) (by omega) (by omega)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact accessible_sub hw (Or.inr rfl) (by omega) (by omega)
  · dsimp only
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.reducePow]
    have := (s.regs 29).isLt
    omega
  · dsimp only
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.reducePow]
    have := (s.regs 30).isLt
    omega
end Fv256.Arm64.Pd
