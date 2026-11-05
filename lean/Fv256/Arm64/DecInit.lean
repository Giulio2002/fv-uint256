import Extracted
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.Arm64.DecT
import Fv256.Arm64.DecA
import Fv256.UtilB2
import Fv256.Util

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec
open Fv256.E

namespace Fv256.Arm64.Dec

abbrev decE : Nat := Extracted.entry
/-- The loop head of `Dec` (arm64): the first iteration's block, `JMP 19(PC)` target. -/
abbrev decH : Nat := Extracted.entry + 0x110

/-- The memory of `Dec` at the loop head, from the entry memory `m` (`r` = entry `SP`, `zp` = the receiver,
`a29`/`a30` = the saved `X29`/`X30`). -/
def initMem (m : Janus.Arm64.Memory) (r zp a29 a30 : Nat) : Janus.Arm64.Memory :=
  ((((((((((((((((((((((((m.writeLE (r - 392) 8 a29).writeLE (r - 384) 8 a30).writeLE (r - 290) 16 64053151420411946063694043751862251568).writeLE
    (r - 274) 16 64053151420411946063694043751862251568).writeLE (r - 258) 16 64053151420411946063694043751862251568).writeLE
    (r - 242) 16 64053151420411946063694043751862251568).writeLE (r - 226) 16 64053151420411946063694043751862251568).writeLE
    (r - 210) 16 64053151420411946063694043751862251568).writeLE (r - 200) 8 3472328296227680304).writeLE
    (r - 64) 8 0).writeLE (r - 56) 8 0).writeLE (r - 48) 8 0).writeLE (r - 40) 8 0).writeLE (r - 64) 8 10000000000000000000).writeLE
    (r - 96) 8 0).writeLE (r - 88) 8 0).writeLE (r - 80) 8 0).writeLE (r - 72) 8 0).writeLE
    (r - 96) 8 (m.readLE zp 8)).writeLE (r - 88) 8 (m.readLE (zp + 8) 8)).writeLE
    (r - 80) 8 (m.readLE (zp + 16) 8)).writeLE (r - 72) 8 (m.readLE (zp + 24) 8)).writeLE (r - 309) 8 0).writeLE
    (r - 301) 8 0).writeLE (r - 298) 8 0

set_option maxRecDepth 200000 in
theorem initMem_frame (m : Janus.Arm64.Memory) (r zp a29 a30 : Nat) (h : 392 ≤ r) :
    MemFrame m (initMem m r zp a29 a30) [(r - 392, r - 32)] := by
  unfold initMem
  repeat' first
    | exact MemFrame.refl _ _
    | refine MemFrame.writeLE ?_ _ (List.mem_singleton_self _) (by omega) (by omega)

set_option maxRecDepth 200000 in
theorem initMem_save1 (m : Janus.Arm64.Memory) (r zp a29 a30 : Nat) (h : 392 ≤ r) (hb : a29 < 2 ^ 64) :
    (initMem m r zp a29 a30).readLE (r - 392) 8 = a29 := by
  unfold initMem
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  simp only [Nat.reducePow]
  omega

set_option maxRecDepth 200000 in
theorem initMem_save2 (m : Janus.Arm64.Memory) (r zp a29 a30 : Nat) (h : 392 ≤ r) (hb : a30 < 2 ^ 64) :
    (initMem m r zp a29 a30).readLE (r - 384) 8 = a30 := by
  unfold initMem
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  simp only [Nat.reducePow]
  omega

set_option maxRecDepth 200000 in
theorem initMem_y (m : Janus.Arm64.Memory) (r zp a29 a30 : Nat) (h : 392 ≤ r) :
    (initMem m r zp a29 a30).readLE (r - 96) 32 = m.readLE zp 32 := by
  rw [Util.readLE_32, Util.readLE_32, show r - 96 + 8 = r - 88 by omega, show r - 96 + 16 = r - 80 by omega, show r - 96 + 24 = r - 72 by omega]
  unfold initMem
  have l0 := Janus.Arm64.Memory.readLE_lt m zp 8
  have l1 := Janus.Arm64.Memory.readLE_lt m (zp + 8) 8
  have l2 := Janus.Arm64.Memory.readLE_lt m (zp + 16) 8
  have l3 := Janus.Arm64.Memory.readLE_lt m (zp + 24) 8
  simp only [Nat.reducePow] at l0 l1 l2 l3
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  simp only [Nat.reducePow, Nat.add_assoc]
  omega

theorem zbyte_all : ∀ e, e < 16 → 64053151420411946063694043751862251568 / 256 ^ e % 256 ^ 1 = 48 := by
  decide +kernel
theorem zbyte8_all : ∀ e, e < 8 → 3472328296227680304 / 256 ^ e % 256 ^ 1 = 48 := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem initMem_d (m : Janus.Arm64.Memory) (r zp a29 a30 : Nat) (h : 392 ≤ r) :
    (initMem m r zp a29 a30).readLE (r - 64) 32 = 10 ^ 19 := by
  rw [Util.readLE_32, show r - 64 + 8 = r - 56 by omega, show r - 64 + 16 = r - 48 by omega, show r - 64 + 24 = r - 40 by omega]
  unfold initMem
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  all_goals (try simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv])
  all_goals omega

set_option maxRecDepth 200000 in
theorem initMem_zeros (m : Janus.Arm64.Memory) (r zp a29 a30 : Nat) (h : 392 ≤ r) :
    ∀ i, i < 98 → (initMem m r zp a29 a30).readLE (r - 290 + i) 1 = 48 := by
  intro i hi
  unfold initMem
  by_cases c1 : 90 ≤ i
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
    exact zbyte8_all _ (by omega)
  by_cases c2 : 80 ≤ i
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
    exact zbyte_all _ (by omega)
  by_cases c3 : 64 ≤ i
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
    exact zbyte_all _ (by omega)
  by_cases c4 : 48 ≤ i
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
    exact zbyte_all _ (by omega)
  by_cases c5 : 32 ≤ i
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
    exact zbyte_all _ (by omega)
  by_cases c6 : 16 ≤ i
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
    exact zbyte_all _ (by omega)
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
    exact zbyte_all _ (by omega)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem dec_init (s : State) (hpc : s.pc = BitVec.ofNat 64 decE) (zp : Nat) (e0 : s.regs 0 = BitVec.ofNat 64 zp)
    (hg : GuardOK s 256) (hal : s.sp.toNat % 16 = 0) (h392 : 392 ≤ s.sp.toNat) (hsp2 : s.sp.toNat < 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 392) 392 true = true)
    (hd : Extracted.program.DataLoaded s.mem)
    (hz : zp + 32 ≤ 2 ^ 48 ∧ s.mem.accessible zp 32 false = true)
    (hzd : zp + 32 ≤ s.sp.toNat - 392 ∨ s.sp.toNat ≤ zp)
    (hret : (s.regs 30).toNat < 2 ^ 48)
    (hbig : s.mem.readLE (zp + 8) 8 ≠ 0 ∨ s.mem.readLE (zp + 16) 8 ≠ 0 ∨ s.mem.readLE (zp + 24) 8 ≠ 0) :
    ReachesRet Extracted.program (BitVec.ofNat 64 decH) s
      (fun S' => S'.regs 0 = BitVec.ofNat 64 98 ∧ S'.regs 1 = 19#64 ∧
        S'.regs 3 = BitVec.ofNat 64 (s.sp.toNat - 96) ∧ S'.regs 6 = BitVec.ofNat 64 (s.sp.toNat - 64) ∧
        S'.regs 8 = BitVec.ofNat 64 (s.sp.toNat - 309) ∧ S'.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 392) ∧
        S'.sp = BitVec.ofNat 64 (s.sp.toNat - 384) ∧
        (∀ k, k ∉ [0, 1, 3, 6, 8, 9, 10, 11, 12, 16, 17, 20, 25, 29] → S'.regs k = s.regs k) ∧
        MemFrame s.mem S'.mem [(s.sp.toNat - 392, s.sp.toNat - 32)] ∧
        Fv256.B.wv S'.mem (s.sp.toNat - 96) 4 = Fv256.B.wv s.mem zp 4 ∧
        Fv256.B.wv S'.mem (s.sp.toNat - 64) 4 = 10 ^ 19 ∧
        (∀ k, k < 98 → S'.mem.readLE (s.sp.toNat - 384 + 94 + 97 - k) 1 = 48) ∧ TabsOK S'.mem ∧
        S'.mem.readLE (s.sp.toNat - 392) 8 = (s.regs 29).toNat ∧ S'.mem.readLE (s.sp.toNat - 384) 8 = (s.regs 30).toNat) := by
  have hc : decE + 0x400 < 2 ^ 47 := by decide
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hzn, hza⟩ := hz
  janus_data hd [hw]
  have l0 := Janus.Arm64.Memory.readLE_lt s.mem zp 8
  have l1 := Janus.Arm64.Memory.readLE_lt s.mem (zp + 8) 8
  have l2 := Janus.Arm64.Memory.readLE_lt s.mem (zp + 16) 8
  have l3 := Janus.Arm64.Memory.readLE_lt s.mem (zp + 24) 8
  simp only [Nat.reducePow] at l0 l1 l2 l3
  have hnz : ((BitVec.ofNat 64 (s.mem.readLE zp 8) ||| BitVec.ofNat 64 (s.mem.readLE (zp + 8) 8) |||
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
  have hnz2 : ((BitVec.ofNat 64 (s.mem.readLE (zp + 8) 8) ||| BitVec.ofNat 64 (s.mem.readLE (zp + 16) 8) |||
      BitVec.ofNat 64 (s.mem.readLE (zp + 24) 8)).toNat = 0) = False := by
    apply eq_false
    intro h
    rw [BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 8) 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 16) 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 24) 8 < 2 ^ 64)] at h
    simp only [Nat.or_eq_zero_iff] at h
    omega
  janus_run [e0, Nat.or_eq_zero_iff] until [decH]
  have hr := s.sp.isLt
  have hr0 : 392 ≤ s.sp.toNat := h392
  refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setReg]
  · simp [setReg]
  · simp [setReg]; exact Fv256.E.bv_sub_lit _ 96 (by omega)
  · simp [setReg]; exact Fv256.E.bv_sub_lit _ 64 (by omega)
  · simp [setReg]; exact Fv256.E.bv_sub_lit _ 309 (by omega)
  · simp [setReg]; exact Fv256.E.bv_sub_lit _ 392 (by omega)
  · simp; exact Fv256.E.bv_sub_lit _ 384 (by omega)
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setReg, hk]
  · exact initMem_frame s.mem s.sp.toNat zp (s.regs 29).toNat (s.regs 30).toNat hr0
  · rw [Fv256.B.wv4_eq, Fv256.B.wv4_eq]
    exact initMem_y s.mem s.sp.toNat zp (s.regs 29).toNat (s.regs 30).toNat hr0
  · rw [Fv256.B.wv4_eq]
    exact initMem_d s.mem s.sp.toNat zp (s.regs 29).toNat (s.regs 30).toNat hr0
  · intro k hk
    rw [show s.sp.toNat - 384 + 94 + 97 - k = s.sp.toNat - 290 + (97 - k) by omega]
    exact initMem_zeros s.mem s.sp.toNat zp (s.regs 29).toNat (s.regs 30).toNat hr0 _ (by omega)
  · refine TabsOK.frame (TabsOK.of_loaded hd) (rs := [(s.sp.toNat - 392, s.sp.toNat - 32)]) ?_ ?_
    · exact initMem_frame s.mem s.sp.toNat zp (s.regs 29).toNat (s.regs 30).toNat hr0
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact accessible_sub hw (Or.inr rfl) (by omega) (by omega)
  · exact initMem_save1 s.mem s.sp.toNat zp (s.regs 29).toNat (s.regs 30).toNat hr0 (by have := (s.regs 29).isLt; omega)
  · exact initMem_save2 s.mem s.sp.toNat zp (s.regs 29).toNat (s.regs 30).toNat hr0 (by have := (s.regs 30).isLt; omega)
end Fv256.Arm64.Dec
