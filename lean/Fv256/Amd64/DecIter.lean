import Extracted
import Fv256.SpecE
import Fv256.UtilE
import Fv256.Amd64.DecA
import Fv256.Amd64.DecInit
import Fv256.Amd64.StrconvMemmove
import Fv256.Amd64.StrconvAppend
import Fv256.Amd64.UdivremM
import Fv256.UtilB2
import Fv256.Amd64.DecT
import Fv256.Util

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E

namespace Fv256.Amd64.Dec

/-- The branch of `Dec`'s loop after the copy: `JNE` at `0x2e3`. -/
def decBr : Nat := decE + 0x2e3

local macro "rs" : tactic => `(tactic| simp [setRegF, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.stackguard0Offset, Janus.Amd64.GoABI.stackguard0])

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem dec_iter (s : State) (b pos y : Nat) (M : Memory) (hpc : s.rip = BitVec.ofNat 64 decH) (hM : s.mem = M)
    (hy0 : y ≠ 0) (hy1 : y < 2 ^ 256) (hpos : 19 ≤ pos) (hpos2 : pos ≤ 98)
    (hb : 0x1a0 ≤ b) (hb8 : b % 8 = 0) (hb2 : b + 0x180 ≤ 2 ^ 48)
    (hw : M.accessible (b - 0x1a0) (0x1a0 + 0x180) true = true)
    (hd : TabsOK M)
    (hx15 : s.xmm 15 = 0) (hdf : s.df = false)
    (e0 : s.regs 0 = BitVec.ofNat 64 pos) (e1 : s.regs 1 = 19#64) (e2 : s.regs 2 = BitVec.ofNat 64 (b + 67))
    (e7 : s.regs 7 = BitVec.ofNat 64 (b + 280)) (e9 : s.regs 9 = BitVec.ofNat 64 (b + 312)) (e4 : s.regs 4 = BitVec.ofNat 64 b)
    (e5 : s.regs 5 = BitVec.ofNat 64 (b + 368))
    (hg3 : M.readLE ((s.regs 14).toNat + 16) 8 + 0x200 < b) (hg1 : (s.regs 14).toNat + 24 ≤ 2 ^ 48)
    (hg2 : M.accessible ((s.regs 14).toNat + 16) 8 false = true)
    (hgd : (s.regs 14).toNat + 16 + 8 ≤ b - 0x1a0 ∨ b + 0x180 ≤ (s.regs 14).toNat + 16)
    (hym : Fv256.B.wv M (b + 280) 4 = y) (hdm : Fv256.B.wv M (b + 312) 4 = 10 ^ 19) :
    ReachesRet Extracted.program (BitVec.ofNat 64 decBr)
      s
      (fun S' => S'.regs 0 = BitVec.ofNat 64 (b + 67) ∧ S'.regs 1 = 19#64 ∧
        S'.regs 2 = BitVec.ofNat 64 (b + (pos - decLen (y % 10 ^ 19)) + 86) ∧ S'.regs 4 = BitVec.ofNat 64 b ∧
        S'.regs 5 = BitVec.ofNat 64 (b + 368) ∧ S'.regs 11 = BitVec.ofNat 64 pos ∧
        S'.regs 13 = BitVec.ofNat 64 (98 - (pos - decLen (y % 10 ^ 19))) ∧ S'.regs 14 = s.regs 14 ∧
        S'.xmm 15 = 0 ∧ S'.df = false ∧
        (∃ pf sf, S'.flags = { cf := some false, pf := pf, af := none, zf := some (decide (y / 10 ^ 19 = 0)), sf := sf, ovf := some false }) ∧
        Fv256.B.wv S'.mem (b + 280) 4 = y / 10 ^ 19 ∧ Fv256.B.wv S'.mem (b + 312) 4 = 10 ^ 19 ∧
        (∀ k, k < decLen (y % 10 ^ 19) → S'.mem.readLE (b + 86 + pos - 1 - k) 1 = 48 + y / 10 ^ k % 10) ∧
        MemFrame M S'.mem [(b - 0x1a0, b + 86), (b + (pos - decLen (y % 10 ^ 19)) + 86, b + 86 + pos), (b + 184, b + 368)] ∧
        TabsOK S'.mem) := by
  have hc : decE + 0x5000 < 2 ^ 47 := by decide
  have hc2 : decH + 0x5000 < 2 ^ 47 := by decide
  tabs_data hd [hw]
  have hdnz : ¬ (M.readLE (b + 312) 8 + 18446744073709551616 * M.readLE (b + 312 + 8) 8 +
      340282366920938463463374607431768211456 * M.readLE (b + 312 + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * M.readLE (b + 312 + 24) 8 = 0) := by
    intro h
    have h2 := hdm
    simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at h2
    omega
  janus64_run [e0, e1, e2, e7, e9, e4, e5, Fv256.Util.readLE_32, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.B.wv4_eq, hdm, hdnz, Fv256.B.bv128_zero_toNat] until [au] calls [Fv256.Amd64.UdivremM.udivrem_rem_s]
  rename_i R1 fl1 X1 M1 kr1 hq hrm hfr
  have hfrM : MemFrame M M1 [(b - 0x1a0, b + 0x180)] := by
    refine MemFrame.trans (rs := [(b - 0x1a0, b + 0x180)]) (rs' := [(b - 0x1a0, b + 0x180)]) ?_ (hfr.mono ?_)
      (fun a n h => ⟨h, h⟩)
    · repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (List.mem_singleton_self _) (by omega) (by omega)
    · intro a n h
      simp only [Outside, and_true] at h ⊢
      omega
  have hwr : ∀ r ∈ [(b - 0x1a0, b + 0x180)], M.accessible r.1 (r.2 - r.1) true = true := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact accessible_sub hw (Or.inr rfl) (by omega) (by omega)
  have hM1 : TabsOK M1 := hd.frame hfrM hwr
  have hg3' : M1.readLE ((s.regs 14).toNat + 16) 8 = M.readLE ((s.regs 14).toNat + 16) 8 :=
    hfrM.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hg2' : M1.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hfrM.accessible]; exact hg2
  have hw1 : M1.accessible (b - 0x1a0) (0x1a0 + 0x180) true = true := by rw [hfrM.accessible]; exact hw
  have hl : ∀ a, M1.readLE a 8 < 2 ^ 64 := fun a => by simpa using Janus.Arm64.Memory.readLE_lt M1 a 8
  have hyx : M.readLE (b + 280) 8 + 18446744073709551616 * M.readLE (b + 280 + 8) 8 +
      340282366920938463463374607431768211456 * M.readLE (b + 280 + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * M.readLE (b + 280 + 24) 8 = y := by
    have h2 := hym
    simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at h2
    simp only [Nat.add_assoc, Nat.reduceAdd]
    omega
  have hdx : M.readLE (b + 312) 8 + 18446744073709551616 * M.readLE (b + 312 + 8) 8 +
      340282366920938463463374607431768211456 * M.readLE (b + 312 + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * M.readLE (b + 312 + 24) 8 = 10 ^ 19 := by
    have h2 := hdm
    simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at h2
    simp only [Nat.add_assoc, Nat.reduceAdd]
    omega
  rw [hyx, hdx, Fv256.B.divSpec_of_ne _ _ (by decide)] at hq
  rw [hyx, hdx, Fv256.B.modSpec_of_ne _ _ (by decide)] at hrm
  have hrlt : y % 10 ^ 19 < 10 ^ 19 := Nat.mod_lt _ (by decide)
  have h19 : 10 ^ 19 < 2 ^ 64 := by decide
  have hr0 : M1.readLE (b + 184) 8 = y % 10 ^ 19 ∧ M1.readLE (b + 184 + 8) 8 = 0 ∧ M1.readLE (b + 184 + 16) 8 = 0 ∧
      M1.readLE (b + 184 + 24) 8 = 0 := by
    have := hl (b + 184); have := hl (b + 184 + 8); have := hl (b + 184 + 16); have := hl (b + 184 + 24)
    omega
  refine ReachesRet.call append_summary ?_ ?_ ?_
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
      have hbb : BitVec.toNat (BitVec.ofNat 64 (M1.readLE (b + 184) 8)) = y % 10 ^ 19 := by
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
    have e67 : (b + 67) % 18446744073709551616 = b + 67 := by omega
    have e8 : (18446744073709551608 + b) % 18446744073709551616 = b - 8 := by omega
    simp only [e67, e8] at bfr bdig
    have hnd : decLen (M1.readLE (b + 184) 8) = decLen (y % 10 ^ 19) := by rw [hr0.1]
    rw [hnd] at b3 bfr bdig
    rw [hr0.1] at bdig
    have hnd19 : decLen (y % 10 ^ 19) ≤ 19 := decLen_le_of_lt_pow _ 19 (by decide) hrlt
    have hnd1 := decLen_pos (y % 10 ^ 19)
    generalize hndd : decLen (y % 10 ^ 19) = nd at b3 bfr bdig hnd19 hnd1
    have hwaS : sA.mem.accessible (b - 0x1a0) (0x1a0 + 0x180) true = true := by
      rw [bfr.accessible]
      simp only [Janus.Arm64.Memory.accessible_writeLE]
      exact hw1
    -- the spill slots written before the call keep their values
    have hS0 : ∀ a n, (a + n ≤ b + 280 ∨ b + 312 ≤ a) → (a + n ≤ b - 8 ∨ b ≤ a) → (a + n ≤ b + 67 ∨ b + 67 + decLen (y % 10 ^ 19) ≤ a) →
        (a + n ≤ b - 144 ∨ b + 24 ≤ a) → sA.mem.readLE a n = M1.readLE a n := by
      intro a n h1 h2 h3 h4
      rw [bfr.readLE a n (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have hs248 : sA.mem.readLE (b + 248) 8 = pos := by
      rw [hS0 _ _ (by omega) (by omega) (by omega) (by omega), hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [Janus.Arm64.Memory.readLE_writeLE_self]
      try exact Nat.mod_eq_of_lt (by omega)
    have hs256 : sA.mem.readLE (b + 256) 8 = 19 := by
      rw [hS0 _ _ (by omega) (by omega) (by omega) (by omega), hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [Janus.Arm64.Memory.readLE_writeLE_self]
      try exact Nat.mod_eq_of_lt (by omega)
    have hs344 : sA.mem.readLE (b + 344) 8 = b + 67 := by
      rw [hS0 _ _ (by omega) (by omega) (by omega) (by omega), hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [Janus.Arm64.Memory.readLE_writeLE_self]
      try exact Nat.mod_eq_of_lt (by omega)
    have b3' : sA.regs 3 = BitVec.ofNat 64 nd := by
      apply BitVec.eq_of_toNat_eq
      rw [b3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show nd < 2 ^ 64 by omega)]
    have hsub : BitVec.ofNat 64 pos - BitVec.ofNat 64 nd = BitVec.ofNat 64 (pos - nd) :=
      Fv256.E.ofNat_sub_ofNat _ _ (by omega) (by omega)
    have hneg := neg98 (pos - nd) (by omega)
    have hmask3 := mask98 (pos - nd) (by omega)
    have hmin : (if (nd : Int) < ((98 - (pos - nd) : Nat) : Int) then BitVec.ofNat 64 nd else BitVec.ofNat 64 (98 - (pos - nd))) =
        BitVec.ofNat 64 nd := by
      split
      · rfl
      · rename_i hh
        have : nd = 98 - (pos - nd) := by omega
        exact congrArg (BitVec.ofNat 64) this.symm
    janus64_run [b3', hsub, hneg, hmask3, hmin] until [decBr] calls [memmove_sum]
    rename_i a0 hrip2 hr42 hx2 hdf2 hmx2 hdl2 hrg2 hby2 hfr2
    simp [setRegF] at hr42 hdf2 hmx2 hrg2 bdf bmx
    have hdst_out : ∀ a n, (a + n ≤ b + (pos - nd) + 86 ∨ b + (pos - nd) + 86 + nd ≤ a) → s'.mem.readLE a n = (((((sA.mem.writeLE (b + 272) 8 19).writeLE (b + 360) 8 (b + 67)).writeLE (b + 264) 8 (98 - (pos - nd))).writeLE (b + 352) 8 (b + (pos - nd) + 86)).writeLE (b - 8) 8 4931827).readLE a n := by
      intro a n h
      exact hfr2.readLE a n (by simp only [Outside, and_true]; omega)
    have hy_limb : ∀ j, j < 4 → s'.mem.readLE (b + 280 + 8 * j) 8 = M1.readLE (b + 216 + 8 * j) 8 := by
      intro j hj
      rw [hdst_out _ _ (by omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [bfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;>
        first | done | (apply Nat.mod_eq_of_lt; simpa using Janus.Arm64.Memory.readLE_lt M1 _ 8)
    have hd_limb : ∀ j, j < 4 → s'.mem.readLE (b + 312 + 8 * j) 8 = M.readLE (b + 312 + 8 * j) 8 := by
      intro j hj
      rw [hdst_out _ _ (by omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [hS0 _ _ (by omega) (by omega) (by omega) (by omega), hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    refine ReachesRet.done (by rfl) ?_
    dsimp only
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF]
    · simp [setRegF]
    · simp [setRegF]
    · simp [setRegF]
      rw [hr42]
      exact BitVec.sub_add_cancel _ _
    · have := hrg2 5 (by simp)
      simp [b5] at this
      exact this
    · simp [setRegF]
    · simp [setRegF]
    · have := hrg2 14 (by simp)
      simp [b14] at this
      exact this
    · rw [hx2 15 (by omega)]; exact bx
    · rfl
    · -- the zero flag of the quotient test
      have hlq := fun a => Janus.Arm64.Memory.readLE_lt M1 a 8
      simp only [Nat.reducePow] at hlq
      have hz : ((BitVec.ofNat 64 (M1.readLE (b + 224) 8) ||| BitVec.ofNat 64 (M1.readLE (b + 216) 8) |||
          BitVec.ofNat 64 (M1.readLE (b + 232) 8) ||| BitVec.ofNat 64 (M1.readLE (b + 240) 8)).toNat = 0) ↔ y / 10 ^ 19 = 0 := by
        rw [Fv256.E.or4_toNat_zero_iff _ _ _ _ (hlq _) (hlq _) (hlq _) (hlq _)]
        have := hlq (b + 216); have := hlq (b + 216 + 8); have := hlq (b + 216 + 16); have := hlq (b + 216 + 24)
        have e8 : b + 216 + 8 = b + 224 := by omega
        have e16 : b + 216 + 16 = b + 232 := by omega
        have e24 : b + 216 + 24 = b + 240 := by omega
        rw [e8, e16, e24] at *
        omega
      refine Fv256.E.flags_exists _ _ rfl rfl ?_ rfl
      dsimp only
      rw [decide_eq_decide.mpr hz]
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
      have hb := hby2 (nd - 1 - k) (by omega)
      rw [show b + 86 + pos - 1 - k = b + (pos - nd) + 86 + (nd - 1 - k) by omega, hb]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [Janus.Arm64.Memory.readLE_one, show b + 67 + (nd - 1 - k) = b + 67 + nd - 1 - k by omega, bdig k hk,
        Fv256.E.digit_mod y k 19 (by omega)]
    · have tr : ∀ {m1 m2 m3 : Memory}, MemFrame m1 m2 [(b - 0x1a0, b + 86), (b + (pos - nd) + 86, b + 86 + pos), (b + 184, b + 368)] →
          MemFrame m2 m3 [(b - 0x1a0, b + 86), (b + (pos - nd) + 86, b + 86 + pos), (b + 184, b + 368)] →
          MemFrame m1 m3 [(b - 0x1a0, b + 86), (b + (pos - nd) + 86, b + 86 + pos), (b + 184, b + 368)] :=
        fun h h' => h.trans h' (fun a n h => ⟨h, h⟩)
      have wr : ∀ {m1 m2 : Memory} {a k v : Nat}, MemFrame m1 m2 [(b - 0x1a0, b + 86), (b + (pos - nd) + 86, b + 86 + pos), (b + 184, b + 368)] →
          ((b - 0x1a0 ≤ a ∧ a + k ≤ b + 86) ∨ (b + (pos - nd) + 86 ≤ a ∧ a + k ≤ b + 86 + pos) ∨ (b + 184 ≤ a ∧ a + k ≤ b + 368)) →
          MemFrame m1 (m2.writeLE a k v) [(b - 0x1a0, b + 86), (b + (pos - nd) + 86, b + 86 + pos), (b + 184, b + 368)] := by
        intro m1 m2 a k v h hr
        rcases hr with hr | hr | hr
        · exact h.writeLE v (List.mem_cons_self ..) hr.1 hr.2
        · exact h.writeLE v (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hr.1 hr.2
        · exact h.writeLE v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) hr.1 hr.2
      refine tr ?_ (tr (hfr.mono ?_) (tr ?_ (tr (bfr.mono ?_) (tr ?_ (hfr2.mono ?_)))))
      · repeat' first
          | exact MemFrame.refl _ _
          | (refine wr ?_ (by omega))
      · intro a n h
        simp only [Outside, and_true] at h ⊢
        omega
      · repeat' first
          | exact MemFrame.refl _ _
          | (refine wr ?_ (by omega))
      · intro a n h
        simp only [Outside, and_true] at h ⊢
        omega
      · repeat' first
          | exact MemFrame.refl _ _
          | (refine wr ?_ (by omega))
      · intro a n h
        simp only [Outside, and_true] at h ⊢
        omega
    · refine hdl2 ?_
      repeat' first
        | exact btab
        | refine TabsOK.writeLE ?_ ?_ _
        | (simp only [Janus.Arm64.Memory.accessible_writeLE]; exact accessible_sub hwaS (Or.inr rfl) (by omega) (by omega))
        | exact accessible_sub hwaS (Or.inr rfl) (by omega) (by omega)
end Fv256.Amd64.Dec
