import Fv256.Arm64.PrettyProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.PdCells
import Fv256.Arm64.P.A
import Fv256.Arm64.P.T
import Fv256.Arm64.P.Append
import Fv256.Arm64.ChainProg
import Fv256.Arm64.CodeIn
import Fv256.Arm64.UdivremFinal
import Fv256.UtilB2
import Fv256.Util
import Fv256.Arm64.Pd.Init

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec
open Fv256.E Fv256.Arm64.P Fv256.Arm64.Pd

namespace Fv256.Arm64.Pd

set_option maxRecDepth 200000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ChainProg.program Fv256.Arm64.PrettyProg.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 200000 in
theorem hcStr : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.StrProg.program Fv256.Arm64.PrettyProg.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

/-- the inner copy loop head (`TBNZ X8, #63`) -/
def pdI : Nat := pdE + 0x190
/-- after the inner loop (`LDP X8, X12, [SP, #320]`) -/
def pdJ : Nat := pdE + 0x1cc
/-- the pad loop head -/
def pdK : Nat := pdE + 0x1f8
/-- the tail: `y == 0`, to the `slicebytetostring` call -/
def pdF : Nat := pdE + 0x234

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- One chunk, first half: from the loop head through `udivrem`, `AppendUint` and the reload of the registers to the inner copy
loop head `pdI`.  `y` is the current quotient, `c` the cells produced so far, `sepb` the separator byte; `b` is the body `SP`. -/
theorem pd_iter1 (s : State) (b c y sepb : Nat) (M : Memory) (hpc : s.pc = BitVec.ofNat 64 pdH) (hM : s.mem = M)
    (hy0 : y ≠ 0) (hy1 : y < 2 ^ 256) (hc : c ≤ 132) (hsb : sepb < 256)
    (hb : 368 ≤ b) (hb16 : b % 16 = 0) (hb2 : b + 424 ≤ 2 ^ 48)
    (hw : M.accessible (b - 368) (368 + 424) true = true)
    (hd : TabsOK M)
    (esp : s.sp = BitVec.ofNat 64 b)
    (e0 : s.regs 0 = 19#64) (e2 : s.regs 2 = BitVec.ofNat 64 (132 - c)) (e3 : s.regs 3 = BitVec.ofNat 64 (b + 320))
    (e4 : s.regs 4 = BitVec.ofNat 64 (c % 4)) (e6 : s.regs 6 = BitVec.ofNat 64 (b + 352))
    (e8 : s.regs 8 = BitVec.ofNat 64 (b + 80))
    (hg3 : M.readLE ((s.regs 28).toNat + 16) 8 + 304 < b) (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48)
    (hg2 : M.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hgd : (s.regs 28).toNat + 16 + 8 ≤ b - 368 ∨ b + 424 ≤ (s.regs 28).toNat + 16)
    (hym : Fv256.B.wv M (b + 320) 4 = y) (hdm : Fv256.B.wv M (b + 352) 4 = 10 ^ 19)
    (hsep : M.readLE (b + 416) 1 = sepb) :
    ReachesRet Fv256.Arm64.PrettyProg.program (BitVec.ofNat 64 pdI) s
      (fun S' => S'.regs 0 = BitVec.ofNat 64 (b + 80) ∧ S'.regs 1 = BitVec.ofNat 64 (decLen (y % 10 ^ 19)) ∧
        S'.regs 2 = 19#64 ∧ S'.regs 8 = BitVec.ofNat 64 (decLen (y % 10 ^ 19) - 1) ∧
        S'.regs 9 = BitVec.ofNat 64 sepb ∧ S'.regs 10 = BitVec.ofNat 64 (132 - c) ∧ S'.regs 11 = BitVec.ofNat 64 (c % 4) ∧
        S'.regs 28 = s.regs 28 ∧ S'.regs 29 = s.regs 29 ∧ S'.regs 18 = s.regs 18 ∧ S'.sp = s.sp ∧
        Fv256.B.wv S'.mem (b + 320) 4 = y / 10 ^ 19 ∧ Fv256.B.wv S'.mem (b + 352) 4 = 10 ^ 19 ∧
        (∀ k, k < decLen (y % 10 ^ 19) → S'.mem.readLE (b + 80 + decLen (y % 10 ^ 19) - 1 - k) 1 = 48 + y / 10 ^ k % 10) ∧
        S'.mem.readLE (b + 416) 1 = sepb ∧
        MemFrame M S'.mem [(b - 368, b + 99), (b + 232, b + 392)] ∧ TabsOK S'.mem) := by
  have hc1 : pdE + 0x5000 < 2 ^ 47 := by decide
  tabs_data hd [hw]
  have hdnz : ¬ (M.readLE (b + 352) 8 + 18446744073709551616 * M.readLE (b + 352 + 8) 8 +
      340282366920938463463374607431768211456 * M.readLE (b + 352 + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * M.readLE (b + 352 + 24) 8 = 0) := by
    intro h
    have h2 := hdm
    simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at h2
    omega
  subst hM
  have hsp : s.sp.toNat = b := by rw [esp, BitVec.toNat_ofNat]; omega
  janus_run [e0, e2, e3, e4, e6, e8, Fv256.Util.readLE_32, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.B.wv4_eq, hdm, hdnz, Fv256.B.bv128_zero_toNat] until [au] calls [Janus.Contracts.EqHashModel.Summary.of_codeIn hcChain (Fv256.Arm64.UdivremFinal.udivrem_rem_L_final (L := 4) (by omega) (by omega))]
  rename_i ha hpcA hspA h18 h28 h29 h30 hregs hq hrm hfr
  simp [setReg] at h18 h28 h29 h30 hspA
  rename State => sU
  have hwr : ∀ r ∈ [(b - 368, b + 99), (b + 232, b + 392)], s.mem.accessible r.1 (r.2 - r.1) true = true := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact accessible_sub hw (Or.inr rfl) (by omega) (by omega)
    · exact accessible_sub hw (Or.inr rfl) (by omega) (by omega)
  have wr : ∀ {m1 m2 : Memory} {a k v : Nat}, MemFrame m1 m2 [(b - 368, b + 99), (b + 232, b + 392)] →
      ((b - 368 ≤ a ∧ a + k ≤ b + 99) ∨ (b + 232 ≤ a ∧ a + k ≤ b + 392)) →
      MemFrame m1 (m2.writeLE a k v) [(b - 368, b + 99), (b + 232, b + 392)] := by
    intro m1 m2 a k v h hr
    rcases hr with hr | hr
    · exact h.writeLE v (List.mem_cons_self ..) hr.1 hr.2
    · exact h.writeLE v (List.mem_cons_of_mem _ (List.mem_singleton_self _)) hr.1 hr.2
  have hfrM : MemFrame s.mem sU.mem [(b - 368, b + 99), (b + 232, b + 392)] := by
    refine MemFrame.trans (rs := [(b - 368, b + 99), (b + 232, b + 392)]) (rs' := [(b - 368, b + 99), (b + 232, b + 392)]) ?_ (hfr.mono ?_)
      (fun a n h => ⟨h, h⟩)
    · repeat' first
        | exact MemFrame.refl _ _
        | (refine wr ?_ (by omega))
    · intro a n h
      simp only [Outside, and_true] at h ⊢
      omega
  have hM1 : TabsOK sU.mem := hd.frame hfrM hwr
  have hg3' : sU.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hfrM.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hg2' : sU.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hfrM.accessible]; exact hg2
  have hw1 : sU.mem.accessible (b - 368) (368 + 424) true = true := by rw [hfrM.accessible]; exact hw
  have hl : ∀ a, sU.mem.readLE a 8 < 2 ^ 64 := fun a => by simpa using Janus.Arm64.Memory.readLE_lt sU.mem a 8
  have hyx : s.mem.readLE (b + 320) 8 + 18446744073709551616 * s.mem.readLE (b + 320 + 8) 8 +
      340282366920938463463374607431768211456 * s.mem.readLE (b + 320 + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (b + 320 + 24) 8 = y := by
    have h2 := hym
    simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at h2
    simp only [Nat.add_assoc, Nat.reduceAdd]
    omega
  have hdx : s.mem.readLE (b + 352) 8 + 18446744073709551616 * s.mem.readLE (b + 352 + 8) 8 +
      340282366920938463463374607431768211456 * s.mem.readLE (b + 352 + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (b + 352 + 24) 8 = 10 ^ 19 := by
    have h2 := hdm
    simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at h2
    simp only [Nat.add_assoc, Nat.reduceAdd]
    omega
  rw [hyx, hdx] at hq
  rw [hyx, hdx] at hrm
  have hrlt : y % 10 ^ 19 < 10 ^ 19 := Nat.mod_lt _ (by decide)
  have h19 : 10 ^ 19 < 2 ^ 64 := by decide
  have hr0 : sU.mem.readLE (b + 232) 8 = y % 10 ^ 19 ∧ sU.mem.readLE (b + 232 + 8) 8 = 0 ∧
      sU.mem.readLE (b + 232 + 16) 8 = 0 ∧ sU.mem.readLE (b + 232 + 24) 8 = 0 := by
    have := hl (b + 232); have := hl (b + 232 + 8); have := hl (b + 232 + 16); have := hl (b + 232 + 24)
    omega
  refine ReachesRet.call (Janus.Contracts.EqHashModel.Summary.of_codeIn hcStr Fv256.Arm64.P.append_summary) ?_ ?_ ?_
  · rfl
  · have hbn : (BitVec.ofNat 64 b).toNat = b := by rw [BitVec.toNat_ofNat]; omega
    have hnd1 := decLen_pos (y % 10 ^ 19)
    have hnd19 : decLen (y % 10 ^ 19) ≤ 19 := decLen_le_of_lt_pow _ 19 (by decide) hrlt
    have hmod : sU.mem.readLE (b + 232) 8 % 18446744073709551616 = y % 10 ^ 19 := by
      rw [Nat.mod_eq_of_lt (hl _), hr0.1]
    have hacc : ∀ a n, b - 368 ≤ a → a + n ≤ b + 424 → sU.mem.accessible a n true = true :=
      fun a n h1 h2 => accessible_sub hw1 (Or.inr rfl) h1 (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setReg]
    · simp [GuardOK, setReg, hbn, Janus.Arm64.Memory.accessible_writeLE, h28]
      refine ⟨by omega, hg2', ?_⟩
      repeat rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      rw [hg3']; omega
    · simp [hbn]; omega
    · simp [hbn]; omega
    · simp [hbn]; omega
    · simp only [hbn, Janus.Arm64.Memory.accessible_writeLE]
      exact hacc _ _ (by omega) (by omega)
    · repeat' first
        | exact hM1
        | refine TabsOK.writeLE ?_ ?_ _
        | (simp only [Janus.Arm64.Memory.accessible_writeLE, hbn]; exact hacc _ _ (by omega) (by omega))
        | exact hacc _ _ (by omega) (by omega)
    · simp [setReg, hmod]; omega
    · simp [setReg]; omega
    · simp [setReg, hbn, Janus.Arm64.Memory.accessible_writeLE]
      exact hacc _ _ (by omega) (by omega)
    · simp [setReg, hbn]; omega
    · simp [setReg, hbn, h28]; omega
    · simp [setReg]
    · simp [setReg]
  · intro sA hrip ⟨b0, b1, b2, bsp, b29, b28, b18, bdig, bfr, btab⟩
    simp [setReg] at b0 b1 b2 bsp b29 b28 b18 bdig bfr
    have e80 : (b + 80) % 18446744073709551616 = b + 80 := by omega
    have e0' : b % 18446744073709551616 = b := by omega
    simp only [e80, e0'] at bdig bfr
    rw [hr0.1] at bdig bfr b1
    have hnd19 : decLen (y % 10 ^ 19) ≤ 19 := decLen_le_of_lt_pow _ 19 (by decide) hrlt
    have hnd1 := decLen_pos (y % 10 ^ 19)
    generalize hndd : decLen (y % 10 ^ 19) = nd at b1 bfr bdig hnd19 hnd1 ⊢
    have b1' : sA.regs 1 = BitVec.ofNat 64 nd := by
      apply BitVec.eq_of_toNat_eq
      rw [b1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hs296 : sA.mem.readLE (b + 296) 8 = 132 - c := by
      rw [bfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      try exact Nat.mod_eq_of_lt (by omega)
    have hs304 : sA.mem.readLE (b + 304) 8 = c % 4 := by
      rw [bfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      try exact Nat.mod_eq_of_lt (by omega)
    have hs416 : sA.mem.readLE (b + 416) 1 = sepb := by
      rw [bfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      exact hsep
    have hy_limb : ∀ j, j < 4 → sA.mem.readLE (b + 320 + 8 * j) 8 = sU.mem.readLE (b + 264 + 8 * j) 8 := by
      intro j hj
      rw [bfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;>
        first | done | (apply Nat.mod_eq_of_lt; simpa using Janus.Arm64.Memory.readLE_lt sU.mem _ 8)
    have hd_limb : ∀ j, j < 4 → sA.mem.readLE (b + 352 + 8 * j) 8 = s.mem.readLE (b + 352 + 8 * j) 8 := by
      intro j hj
      rw [bfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have hsx : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 sepb)) = BitVec.ofNat 64 sepb := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    janus_run [b1', hs296, hs304, hs416, hsx] until [pdI]
    refine ReachesRet.done (by rfl) ?_
    dsimp only
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setReg]; exact b0
    · simp [setReg]; exact b1'
    · simp [setReg]; exact b2
    · simp [setReg]; exact Fv256.E.ofNat_sub_ofNat nd 1 (by omega) (by omega)
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]; rw [b28, h28]
    · simp [setReg]; rw [b29, h29]
    · simp [setReg]; rw [b18, h18]
    · exact esp.symm
    · have h0 := hy_limb 0 (by omega); have h1 := hy_limb 1 (by omega)
      have h2 := hy_limb 2 (by omega); have h3 := hy_limb 3 (by omega)
      simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero, Nat.mul_zero] at h0 h1 h2 h3 ⊢
      simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul] at h0 h1 h2 h3
      rw [h0, h1, h2, h3]
      have := hq
      simp only [Nat.add_assoc, Nat.reduceAdd] at this h0 h1 h2 h3 ⊢
      omega
    · have h0 := hd_limb 0 (by omega); have h1 := hd_limb 1 (by omega)
      have h2 := hd_limb 2 (by omega); have h3 := hd_limb 3 (by omega)
      simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at h0 h1 h2 h3 ⊢
      simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul] at h0 h1 h2 h3
      rw [h0, h1, h2, h3]
      have := hdm
      simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at this
      simp only [Nat.add_assoc, Nat.reduceAdd] at this h0 h1 h2 h3 ⊢
      omega
    · intro k hk
      rw [Janus.Arm64.Memory.readLE_one, bdig k hk]
      have := Fv256.E.digit_mod y k 19 (by omega)
      omega
    · exact hs416
    · refine MemFrame.trans (rs := [(b - 368, b + 99), (b + 232, b + 392)]) (rs' := [(b - 368, b + 99), (b + 232, b + 392)]) hfrM
        (MemFrame.trans (rs := [(b - 368, b + 99), (b + 232, b + 392)]) (rs' := [(b - 368, b + 99), (b + 232, b + 392)]) ?_ (bfr.mono ?_)
          (fun a n h => ⟨h, h⟩)) (fun a n h => ⟨h, h⟩)
      · repeat' first
          | exact MemFrame.refl _ _
          | (refine wr ?_ (by omega))
      · intro a n h
        simp only [Outside, and_true] at h ⊢
        omega
    · exact btab
end Fv256.Arm64.Pd
