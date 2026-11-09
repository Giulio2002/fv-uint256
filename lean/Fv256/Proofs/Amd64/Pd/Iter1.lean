import Fv256.Proofs.Common.PrettyProg
import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.UtilE
import Fv256.Proofs.Common.PdCells
import Fv256.Proofs.Amd64.P.A
import Fv256.Proofs.Amd64.P.T
import Fv256.Proofs.Amd64.P.Append
import Fv256.Proofs.Amd64.P.Memmove
import Fv256.Proofs.Common.ChainProg
import Fv256.Proofs.Common.CodeIn
import Fv256.Proofs.Amd64.UdivremL
import Fv256.Proofs.Common.UtilB2
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Amd64.Pd.Init

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E Fv256.Amd64.P

namespace Fv256.Amd64.Pd

set_option maxRecDepth 100000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ChainProg.program Fv256.PrettyProg.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcStr : Janus.Contracts.EqHashModel.CodeIn64 Fv256.StrProg.program Fv256.PrettyProg.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

/-- the inner copy loop head (`TESTQ DX, DX`) -/
def pdI : Nat := pdE + 0x240
/-- after the inner loop (`MOVQ 0x138(SP), DX`) -/
def pdJ : Nat := pdE + 0x276
/-- the tail: `y == 0`, to the `slicebytetostring` call -/
def pdF : Nat := pdE + 0x2d6

local macro "rs" : tactic => `(tactic| simp [setRegF, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.stackguard0Offset, Janus.Amd64.GoABI.stackguard0])

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- One chunk, first half: from the loop head through `udivrem`, `AppendUint` and the reload of the registers to the inner copy
loop head `pdI`.  `y` is the current quotient, `c` the cells produced so far, `sepb` the separator byte. -/
theorem pd_iter1 (s : State) (b c y sepb : Nat) (M : Memory) (hpc : s.rip = BitVec.ofNat 64 pdH) (hM : s.mem = M)
    (hy0 : y ≠ 0) (hy1 : y < 2 ^ 256) (hc : c ≤ 132) (hsb : sepb < 256)
    (hb : 0x180 ≤ b) (hb8 : b % 8 = 0) (hb2 : b + 0x198 ≤ 2 ^ 48)
    (hw : M.accessible (b - 0x180) (0x180 + 0x198) true = true)
    (hd : TabsOK M)
    (hx15 : s.xmm 15 = 0) (hdf : s.df = false)
    (e0 : s.regs 0 = BitVec.ofNat 64 19) (e1 : s.regs 1 = BitVec.ofNat 64 (132 - c)) (e2 : s.regs 2 = BitVec.ofNat 64 (b + 0x40))
    (e6 : s.regs 6 = BitVec.ofNat 64 (c % 4)) (e7 : s.regs 7 = BitVec.ofNat 64 (b + 0x130)) (e9 : s.regs 9 = BitVec.ofNat 64 (b + 0x150))
    (e4 : s.regs 4 = BitVec.ofNat 64 b) (e5 : s.regs 5 = BitVec.ofNat 64 (b + 0x178))
    (hg3 : M.readLE ((s.regs 14).toNat + 16) 8 + 0x100 < b) (hg1 : (s.regs 14).toNat + 24 ≤ 2 ^ 48)
    (hg2 : M.accessible ((s.regs 14).toNat + 16) 8 false = true)
    (hgd : (s.regs 14).toNat + 16 + 8 ≤ b - 0x180 ∨ b + 0x198 ≤ (s.regs 14).toNat + 16)
    (hym : Fv256.B.wv M (b + 0x130) 4 = y) (hdm : Fv256.B.wv M (b + 0x150) 4 = 10 ^ 19)
    (hsep : M.readLE (b + 0x190) 1 = sepb) :
    ReachesRet Fv256.PrettyProg.program (BitVec.ofNat 64 pdI) s
      (fun S' => S'.regs 0 = BitVec.ofNat 64 (b + 0x40) ∧ S'.regs 2 = BitVec.ofNat 64 (decLen (y % 10 ^ 19) - 1) ∧
        S'.regs 3 = BitVec.ofNat 64 (decLen (y % 10 ^ 19)) ∧ S'.regs 4 = BitVec.ofNat 64 b ∧
        S'.regs 5 = BitVec.ofNat 64 (b + 0x178) ∧ S'.regs 11 = BitVec.ofNat 64 sepb ∧
        S'.regs 12 = BitVec.ofNat 64 (132 - c) ∧ S'.regs 13 = BitVec.ofNat 64 (c % 4) ∧ S'.regs 14 = s.regs 14 ∧
        S'.xmm 15 = 0 ∧ S'.df = false ∧
        Fv256.B.wv S'.mem (b + 0x130) 4 = y / 10 ^ 19 ∧ Fv256.B.wv S'.mem (b + 0x150) 4 = 10 ^ 19 ∧
        (∀ k, k < decLen (y % 10 ^ 19) → S'.mem.readLE (b + 0x40 + decLen (y % 10 ^ 19) - 1 - k) 1 = 48 + y / 10 ^ k % 10) ∧
        MemFrame M S'.mem [(b - 0x180, b + 83), (b + 216, b + 376)] ∧ TabsOK S'.mem ∧ S'.regs 1 = 19#64) := by
  have hc1 : pdE + 0x5000 < 2 ^ 47 := by decide
  tabs_data hd [hw]
  have hdnz : ¬ (M.readLE (b + 0x150) 8 + 18446744073709551616 * M.readLE (b + 0x150 + 8) 8 +
      340282366920938463463374607431768211456 * M.readLE (b + 0x150 + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * M.readLE (b + 0x150 + 24) 8 = 0) := by
    intro h
    have h2 := hdm
    simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at h2
    omega
  janus64_run [e0, e1, e2, e6, e7, e9, e4, e5, Fv256.Util.readLE_32, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.B.wv4_eq, hdm, hdnz, Fv256.B.bv128_zero_toNat] until [au] calls [Fv256.CodeIn.lib_summary hcChain Fv256.Amd64.UdivremL.udivrem_rem]
  rename_i R1 fl1 X1 M1 kr1 hq hrm hfr
  have wr : ∀ {m1 m2 : Memory} {a k v : Nat}, MemFrame m1 m2 [(b - 0x180, b + 83), (b + 216, b + 376)] →
      ((b - 0x180 ≤ a ∧ a + k ≤ b + 83) ∨ (b + 216 ≤ a ∧ a + k ≤ b + 376)) →
      MemFrame m1 (m2.writeLE a k v) [(b - 0x180, b + 83), (b + 216, b + 376)] := by
    intro m1 m2 a k v h hr
    rcases hr with hr | hr
    · exact h.writeLE v (List.mem_cons_self ..) hr.1 hr.2
    · exact h.writeLE v (List.mem_cons_of_mem _ (List.mem_singleton_self _)) hr.1 hr.2
  have hfrM : MemFrame M M1 [(b - 0x180, b + 83), (b + 216, b + 376)] := by
    refine MemFrame.trans (rs := [(b - 0x180, b + 83), (b + 216, b + 376)]) (rs' := [(b - 0x180, b + 83), (b + 216, b + 376)]) ?_ (hfr.mono ?_)
      (fun a n h => ⟨h, h⟩)
    · repeat' first
        | exact MemFrame.refl _ _
        | (refine wr ?_ (by omega))
    · intro a n h
      simp only [Outside, and_true] at h ⊢
      omega
  have hwr : ∀ r ∈ [(b - 0x180, b + 83), (b + 216, b + 376)], M.accessible r.1 (r.2 - r.1) true = true := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact accessible_sub hw (Or.inr rfl) (by omega) (by omega)
    · exact accessible_sub hw (Or.inr rfl) (by omega) (by omega)
  have hM1 : TabsOK M1 := hd.frame hfrM hwr
  have hg3' : M1.readLE ((s.regs 14).toNat + 16) 8 = M.readLE ((s.regs 14).toNat + 16) 8 :=
    hfrM.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hg2' : M1.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hfrM.accessible]; exact hg2
  have hw1 : M1.accessible (b - 0x180) (0x180 + 0x198) true = true := by rw [hfrM.accessible]; exact hw
  have hl : ∀ a, M1.readLE a 8 < 2 ^ 64 := fun a => by simpa using Janus.Arm64.Memory.readLE_lt M1 a 8
  have hyx : M.readLE (b + 0x130) 8 + 18446744073709551616 * M.readLE (b + 0x130 + 8) 8 +
      340282366920938463463374607431768211456 * M.readLE (b + 0x130 + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * M.readLE (b + 0x130 + 24) 8 = y := by
    have h2 := hym
    simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at h2
    simp only [Nat.add_assoc, Nat.reduceAdd]
    omega
  have hdx : M.readLE (b + 0x150) 8 + 18446744073709551616 * M.readLE (b + 0x150 + 8) 8 +
      340282366920938463463374607431768211456 * M.readLE (b + 0x150 + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * M.readLE (b + 0x150 + 24) 8 = 10 ^ 19 := by
    have h2 := hdm
    simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at h2
    simp only [Nat.add_assoc, Nat.reduceAdd]
    omega
  rw [hyx, hdx] at hq
  rw [hyx, hdx] at hrm
  have hrlt : y % 10 ^ 19 < 10 ^ 19 := Nat.mod_lt _ (by decide)
  have h19 : 10 ^ 19 < 2 ^ 64 := by decide
  have hr0 : M1.readLE (b + 216) 8 = y % 10 ^ 19 ∧ M1.readLE (b + 216 + 8) 8 = 0 ∧ M1.readLE (b + 216 + 16) 8 = 0 ∧
      M1.readLE (b + 216 + 24) 8 = 0 := by
    have := hl (b + 216); have := hl (b + 216 + 8); have := hl (b + 216 + 16); have := hl (b + 216 + 24)
    omega
  refine ReachesRet.call (Fv256.CodeIn.lib_summary hcStr Fv256.Amd64.P.append_summary) ?_ ?_ ?_
  · rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF]
    · refine ⟨?_, ?_, ?_⟩
      · rs; omega
      · simp only [Janus.Arm64.Memory.accessible_writeLE]
        rs
        exact hg2'
      · rs
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        rw [hg3']; omega
    · refine ⟨?_, ?_, ?_⟩
      · rs; omega
      · rs; omega
      · simp only [Janus.Arm64.Memory.accessible_writeLE]
        rs
        exact accessible_sub hw1 (Or.inr rfl) (by omega) (by omega)
    · rs; omega
    · rs
      have hb8' : (18446744073709551608 + b) % 18446744073709551616 = b - 8 := by omega
      rw [hb8', Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
    · repeat' first
        | exact hM1
        | refine TabsOK.writeLE ?_ ?_ _
        | (simp only [Janus.Arm64.Memory.accessible_writeLE]; exact accessible_sub hw1 (Or.inr rfl) (by omega) (by omega))
        | exact accessible_sub hw1 (Or.inr rfl) (by omega) (by omega)
    · rs
      have hbb : BitVec.toNat (BitVec.ofNat 64 (M1.readLE (b + 216) 8)) = y % 10 ^ 19 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hl _), hr0.1]
      rw [hr0.1]; exact decLen_le_of_lt_pow _ 19 (by decide) hrlt
    · rs; omega
    · simp only [Janus.Arm64.Memory.accessible_writeLE]
      rs
      exact accessible_sub hw1 (Or.inr rfl) (by omega) (by omega)
    · rs; omega
    · rs; omega
  · intro sA hrip ⟨b0, b3, b1, b4, b5, b14, bx, bdf, bmx, bdig, bfr, btab⟩
    simp [setRegF] at b0 b3 b1 b4 b5 b14 bx
    dsimp only at bdig bfr btab
    simp [setRegF, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.regSP] at bfr bdig
    have e8 : (18446744073709551608 + b) % 18446744073709551616 = b - 8 := by omega
    have e64 : (b + 64) % 18446744073709551616 = b + 64 := by omega
    have hnd : decLen (M1.readLE (b + 216) 8) = decLen (y % 10 ^ 19) := by rw [hr0.1]
    rw [hnd] at b3 bfr bdig
    rw [hr0.1] at bdig
    simp only [e8, e64] at bfr bdig
    have hnd19 : decLen (y % 10 ^ 19) ≤ 19 := decLen_le_of_lt_pow _ 19 (by decide) hrlt
    have hnd1 := decLen_pos (y % 10 ^ 19)
    generalize hndd : decLen (y % 10 ^ 19) = nd at b3 bfr bdig hnd19 hnd1 ⊢
    have hwaS : sA.mem.accessible (b - 0x180) (0x180 + 0x198) true = true := by
      rw [bfr.accessible]
      simp only [Janus.Arm64.Memory.accessible_writeLE]
      exact hw1
    have hS0 : ∀ a n, (a + n ≤ b + 304 ∨ b + 336 ≤ a) → (a + n ≤ b - 8 ∨ b ≤ a) → (a + n ≤ b + 64 ∨ b + 64 + nd ≤ a) →
        (a + n ≤ b - 144 ∨ b + 24 ≤ a) → sA.mem.readLE a n = M1.readLE a n := by
      intro a n h1 h2 h3 h4
      rw [bfr.readLE a n (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have hs280 : sA.mem.readLE (b + 280) 8 = 132 - c := by
      rw [hS0 _ _ (by omega) (by omega) (by omega) (by omega), hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [Janus.Arm64.Memory.readLE_writeLE_self]
      try exact Nat.mod_eq_of_lt (by omega)
    have hs288 : sA.mem.readLE (b + 288) 8 = c % 4 := by
      rw [hS0 _ _ (by omega) (by omega) (by omega) (by omega), hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [Janus.Arm64.Memory.readLE_writeLE_self]
      try exact Nat.mod_eq_of_lt (by omega)
    have hs400 : sA.mem.readLE (b + 400) 1 = sepb := by
      rw [hS0 _ _ (by omega) (by omega) (by omega) (by omega), hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      exact hsep
    have b3' : sA.regs 3 = BitVec.ofNat 64 nd := by
      apply BitVec.eq_of_toNat_eq
      rw [b3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show nd < 2 ^ 64 by omega)]
    have hsx : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 sepb)) = BitVec.ofNat 64 sepb := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    have hy_limb : ∀ j, j < 4 → sA.mem.readLE (b + 304 + 8 * j) 8 = M1.readLE (b + 248 + 8 * j) 8 := by
      intro j hj
      rw [bfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;>
        first | done | (apply Nat.mod_eq_of_lt; simpa using Janus.Arm64.Memory.readLE_lt M1 _ 8)
    have hd_limb : ∀ j, j < 4 → sA.mem.readLE (b + 336 + 8 * j) 8 = M.readLE (b + 336 + 8 * j) 8 := by
      intro j hj
      rw [bfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    janus64_run [b3', hs280, hs288, hs400, hsx] until [pdI]
    refine ReachesRet.done (by rfl) ?_
    dsimp only
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF]; exact b0
    · simp [setRegF]; exact Fv256.E.ofNat_sub_ofNat nd 1 (by omega) (by omega)
    · simp [setRegF]; exact b3'
    · simp [setRegF]; rw [b4]; exact BitVec.sub_add_cancel _ _
    · simp [setRegF]; exact b5
    · simp [setRegF, hsx]
    · simp [setRegF]
    · simp [setRegF]
    · simp [setRegF]; exact b14
    · exact bx
    · simpa using bdf.trans hdf
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
    · refine MemFrame.trans (rs := [(b - 0x180, b + 83), (b + 216, b + 376)]) (rs' := [(b - 0x180, b + 83), (b + 216, b + 376)]) hfrM
        (MemFrame.trans (rs := [(b - 0x180, b + 83), (b + 216, b + 376)]) (rs' := [(b - 0x180, b + 83), (b + 216, b + 376)]) ?_ (bfr.mono ?_)
          (fun a n h => ⟨h, h⟩)) (fun a n h => ⟨h, h⟩)
      · repeat' first
          | exact MemFrame.refl _ _
          | (refine wr ?_ (by omega))
      · intro a n h
        simp only [Outside, and_true] at h ⊢
        omega
    · exact btab
    · simp [setRegF]; exact b1
end Fv256.Amd64.Pd
