import Extracted
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.Arm64.DecT
import Fv256.Arm64.DecA
import Fv256.Arm64.DecInit
import Fv256.Arm64.StrconvMemmove
import Fv256.Arm64.StrconvAppend
import Fv256.Arm64.ChainProg
import Fv256.Arm64.CodeIn
import Fv256.Arm64.UdivremFinal
import Fv256.UtilB2
import Fv256.Util

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec
open Fv256.E

namespace Fv256.Arm64.Dec

set_option maxRecDepth 200000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ChainProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

/-- The branch of `Dec`'s loop after the copy: `CBNZ` at `0x1fc`. -/
def decBr : Nat := decE + 0x1fc

set_option maxRecDepth 100000 in
theorem maskLem : ∀ pos, pos < 99 → ∀ k, k < 19 →
    ((BitVec.ofNat 64 pos - (BitVec.ofNat 64 (k + 1) + 98#64)).sshiftRight 63).toNat = 2 ^ 64 - 1 := by
  decide +kernel

theorem ptrLem (pos nd : Nat) (h1 : pos ≤ 98) (h2 : 1 ≤ nd) (h3 : nd ≤ 19) (h4 : nd ≤ pos) :
    ((18446744073709551616 - nd + pos) % 18446744073709551616 &&&
      ((BitVec.ofNat 64 pos - (BitVec.ofNat 64 nd + 98#64)).sshiftRight 63).toNat) = pos - nd := by
  have hm := maskLem pos (by omega) (nd - 1) (by omega)
  rw [show nd - 1 + 1 = nd by omega] at hm
  rw [hm, Nat.and_two_pow_sub_one_of_lt_two_pow (n := 64) (by omega)]
  omega

theorem nLem (pos nd : Nat) (h1 : pos ≤ 98) (h2 : 1 ≤ nd) (h3 : nd ≤ 19) :
    (if (nd : Int) < ((18446744073709551616 - pos + (nd + 98)) % 18446744073709551616 : Nat) then BitVec.ofNat 64 nd
      else BitVec.ofNat 64 nd + 98#64 - BitVec.ofNat 64 pos) = BitVec.ofNat 64 nd := by
  split
  · rfl
  · apply BitVec.eq_of_toNat_eq
    have e98 : (98#64).toNat = 98 := rfl
    rw [BitVec.toNat_sub, BitVec.toNat_add, e98, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : nd < 2 ^ 64), Nat.mod_eq_of_lt (by omega : pos < 2 ^ 64)]
    have : nd + 98 - pos = 0 ∨ True := Or.inr trivial
    rename_i hh
    have e2 : (18446744073709551616 - pos + (nd + 98)) % 18446744073709551616 = nd + 98 - pos := by omega
    rw [e2] at hh
    have : pos = 98 := by omega
    subst this
    omega

theorem or4r (a b c d : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64) (hd : d < 2 ^ 64) :
    (BitVec.ofNat 64 a ||| (BitVec.ofNat 64 b ||| (BitVec.ofNat 64 c ||| BitVec.ofNat 64 d)) = 0#64) ↔
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    rw [BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] at h'
    have h0 : (0#64).toNat = 0 := rfl
    rw [h0] at h'
    simp only [Nat.or_eq_zero_iff] at h'
    simpa using h'
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem dec_iter (s : State) (b pos y : Nat) (M : Memory) (hpc : s.pc = BitVec.ofNat 64 decH) (hM : s.mem = M)
    (hy0 : y ≠ 0) (hy1 : y < 2 ^ 256) (hpos : 19 ≤ pos) (hpos2 : pos ≤ 98)
    (hb : 344 ≤ b) (hb16 : b % 16 = 0) (hb2 : b + 384 ≤ 2 ^ 48)
    (hw : M.accessible (b - 344) (344 + 384) true = true)
    (hd : TabsOK M)
    (e0 : s.regs 0 = BitVec.ofNat 64 pos) (e1 : s.regs 1 = 19#64) (e8 : s.regs 8 = BitVec.ofNat 64 (b + 75))
    (e3 : s.regs 3 = BitVec.ofNat 64 (b + 288)) (e6 : s.regs 6 = BitVec.ofNat 64 (b + 320))
    (esp : s.sp = BitVec.ofNat 64 b)
    (hg3 : M.readLE ((s.regs 28).toNat + 16) 8 + 304 < b) (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48)
    (hg2 : M.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hgd : (s.regs 28).toNat + 16 + 8 ≤ b - 344 ∨ b + 384 ≤ (s.regs 28).toNat + 16)
    (hym : Fv256.B.wv M (b + 288) 4 = y) (hdm : Fv256.B.wv M (b + 320) 4 = 10 ^ 19) :
    ReachesRet Extracted.program (BitVec.ofNat 64 decBr) s
      (fun S' => S'.regs 0 = BitVec.ofNat 64 (b + 75) ∧ S'.regs 2 = 19#64 ∧ S'.regs 8 = BitVec.ofNat 64 pos ∧
        S'.regs 9 = BitVec.ofNat 64 (b + 94 + (pos - decLen (y % 10 ^ 19))) ∧
        S'.regs 11 = BitVec.ofNat 64 (98 - (pos - decLen (y % 10 ^ 19))) ∧
        (S'.regs 10 = 0#64 ↔ y / 10 ^ 19 = 0) ∧ S'.regs 28 = s.regs 28 ∧ S'.regs 29 = s.regs 29 ∧ S'.regs 18 = s.regs 18 ∧ S'.sp = s.sp ∧
        Fv256.B.wv S'.mem (b + 288) 4 = y / 10 ^ 19 ∧ Fv256.B.wv S'.mem (b + 320) 4 = 10 ^ 19 ∧
        (∀ k, k < decLen (y % 10 ^ 19) → S'.mem.readLE (b + 94 + pos - 1 - k) 1 = 48 + y / 10 ^ k % 10) ∧
        MemFrame s.mem S'.mem [(b - 344, b - 8), (b + 8, b + 94), (b + 94 + (pos - decLen (y % 10 ^ 19)), b + 94 + pos), (b + 192, b + 376)] ∧
        TabsOK S'.mem) := by
  have hc : decE + 0x5000 < 2 ^ 47 := by decide
  have hc2 : decH + 0x5000 < 2 ^ 47 := by decide
  tabs_data hd [hw]
  have hdnz : ¬ (M.readLE (b + 320) 8 + 18446744073709551616 * M.readLE (b + 320 + 8) 8 +
      340282366920938463463374607431768211456 * M.readLE (b + 320 + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * M.readLE (b + 320 + 24) 8 = 0) := by
    intro h
    have h2 := hdm
    simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at h2
    omega
  subst hM
  have hsp : s.sp.toNat = b := by rw [esp, BitVec.toNat_ofNat]; omega
  janus_run [e0, e1, e8, e3, e6, Fv256.Util.readLE_32, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.B.wv4_eq, hdm, hdnz, Fv256.B.bv128_zero_toNat] until [au] calls [Janus.Contracts.EqHashModel.Summary.of_codeIn hcChain (Fv256.Arm64.UdivremFinal.udivrem_rem_L_final (L := 4) (by omega) (by omega))]
  rename_i ha hpcA hspA h18 h28 h29 h30 hregs hq hrm hfr
  simp [setReg] at h18 h28 h29 h30 hspA
  rename State => sU
  have hfrM : MemFrame s.mem sU.mem [(b - 344, b + 384)] := by
    refine MemFrame.trans (rs := [(b - 344, b + 384)]) (rs' := [(b - 344, b + 384)]) ?_ (hfr.mono ?_)
      (fun a n h => ⟨h, h⟩)
    · repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (List.mem_singleton_self _) (by omega) (by omega)
    · intro a n h
      simp only [Outside, and_true] at h ⊢
      omega
  have hwr : ∀ r ∈ [(b - 344, b + 384)], s.mem.accessible r.1 (r.2 - r.1) true = true := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact accessible_sub hw (Or.inr rfl) (by omega) (by omega)
  have hM1 : TabsOK sU.mem := hd.frame hfrM hwr
  have hg3' : sU.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hfrM.readLE _ _ (by simp only [Outside, and_true]; omega)
  have hg2' : sU.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hfrM.accessible]; exact hg2
  have hw1 : sU.mem.accessible (b - 344) (344 + 384) true = true := by rw [hfrM.accessible]; exact hw
  have hl : ∀ a, sU.mem.readLE a 8 < 2 ^ 64 := fun a => by simpa using Janus.Arm64.Memory.readLE_lt sU.mem a 8
  have hyx : s.mem.readLE (b + 288) 8 + 18446744073709551616 * s.mem.readLE (b + 288 + 8) 8 +
      340282366920938463463374607431768211456 * s.mem.readLE (b + 288 + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (b + 288 + 24) 8 = y := by
    have h2 := hym
    simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at h2
    simp only [Nat.add_assoc, Nat.reduceAdd]
    omega
  have hdx : s.mem.readLE (b + 320) 8 + 18446744073709551616 * s.mem.readLE (b + 320 + 8) 8 +
      340282366920938463463374607431768211456 * s.mem.readLE (b + 320 + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (b + 320 + 24) 8 = 10 ^ 19 := by
    have h2 := hdm
    simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at h2
    simp only [Nat.add_assoc, Nat.reduceAdd]
    omega
  rw [hyx, hdx] at hq
  rw [hyx, hdx] at hrm
  have hrlt : y % 10 ^ 19 < 10 ^ 19 := Nat.mod_lt _ (by decide)
  have h19 : 10 ^ 19 < 2 ^ 64 := by decide
  have hr0 : sU.mem.readLE (b + 192) 8 = y % 10 ^ 19 ∧ sU.mem.readLE (b + 192 + 8) 8 = 0 ∧
      sU.mem.readLE (b + 192 + 16) 8 = 0 ∧ sU.mem.readLE (b + 192 + 24) 8 = 0 := by
    have := hl (b + 192); have := hl (b + 192 + 8); have := hl (b + 192 + 16); have := hl (b + 192 + 24)
    omega
  refine ReachesRet.call append_summary ?_ ?_ ?_
  · rfl
  · have hbn : (BitVec.ofNat 64 b).toNat = b := by rw [BitVec.toNat_ofNat]; omega
    have hnd1 := decLen_pos (y % 10 ^ 19)
    have hnd19 : decLen (y % 10 ^ 19) ≤ 19 := decLen_le_of_lt_pow _ 19 (by decide) hrlt
    have hmod : sU.mem.readLE (b + 192) 8 % 18446744073709551616 = y % 10 ^ 19 := by
      rw [Nat.mod_eq_of_lt (hl _), hr0.1]
    have hb1 : (BitVec.ofNat 64 (sU.mem.readLE (b + 192) 8)).toNat = y % 10 ^ 19 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hl _), hr0.1]
    have hacc : ∀ a n, b - 344 ≤ a → a + n ≤ b + 384 → sU.mem.accessible a n true = true :=
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
    have e75 : (b + 75) % 18446744073709551616 = b + 75 := by omega
    have e0' : b % 18446744073709551616 = b := by omega
    simp only [e75, e0'] at bdig bfr
    rw [hr0.1] at bdig bfr b1
    have hnd19 : decLen (y % 10 ^ 19) ≤ 19 := decLen_le_of_lt_pow _ 19 (by decide) hrlt
    have hnd1 := decLen_pos (y % 10 ^ 19)
    generalize hndd : decLen (y % 10 ^ 19) = nd at b1 bfr bdig hnd19 hnd1
    have b3' : sA.regs 1 = BitVec.ofNat 64 nd := by
      apply BitVec.eq_of_toNat_eq
      rw [b1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hptr := ptrLem pos nd hpos2 hnd1 hnd19 (by omega)
    have hn := nLem pos nd hpos2 hnd1 hnd19
    janus_run [b0, b2, b3', hptr, hn] until [decBr] calls [memmove_sum]
    rename_i hbrx hpcM hspM hkM hbyM hfrM2
    simp [setReg] at hspM
    have hdst_out : ∀ a n, (a + n ≤ b + 94 + (pos - nd) ∨ b + 94 + (pos - nd) + nd ≤ a) →
        s'.mem.readLE a n = (((((sA.mem.writeLE (b + 280) 8 19).writeLE (b + 368) 8 (b + 75)).writeLE (b + 272) 8
          (18446744073709551616 - pos + (nd + 98))).writeLE (b + 360) 8 (b + 94 + (pos - nd))).readLE a n) := by
      intro a n h
      exact hfrM2.readLE a n (by simp only [Outside, and_true]; omega)
    have hy_limb : ∀ j, j < 4 → s'.mem.readLE (b + 288 + 8 * j) 8 = sU.mem.readLE (b + 224 + 8 * j) 8 := by
      intro j hj
      rw [hdst_out _ _ (by omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [bfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;>
        first | done | (apply Nat.mod_eq_of_lt; simpa using Janus.Arm64.Memory.readLE_lt sU.mem _ 8)
    have hd_limb : ∀ j, j < 4 → s'.mem.readLE (b + 320 + 8 * j) 8 = s.mem.readLE (b + 320 + 8 * j) 8 := by
      intro j hj
      rw [hdst_out _ _ (by omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [bfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    refine ReachesRet.done (by rfl) ?_
    dsimp only
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
      congr 1; omega
    · have hlq := fun a => Janus.Arm64.Memory.readLE_lt sU.mem a 8
      simp only [Nat.reducePow] at hlq
      have hz : ((BitVec.ofNat 64 (sU.mem.readLE (b + 248) 8) ||| (BitVec.ofNat 64 (sU.mem.readLE (b + 240) 8) |||
          (BitVec.ofNat 64 (sU.mem.readLE (b + 232) 8) ||| BitVec.ofNat 64 (sU.mem.readLE (b + 224) 8)))) = 0#64) ↔
          y / 10 ^ 19 = 0 := by
        rw [or4r _ _ _ _ (hlq _) (hlq _) (hlq _) (hlq _)]
        have := hlq (b + 224); have := hlq (b + 224 + 8); have := hlq (b + 224 + 16); have := hlq (b + 224 + 24)
        have e8 : b + 224 + 8 = b + 232 := by omega
        have e16 : b + 224 + 16 = b + 240 := by omega
        have e24 : b + 224 + 24 = b + 248 := by omega
        rw [e8, e16, e24] at *
        omega
      have e : ∀ {X Y : BitVec 64}, X = Y → (X = 0#64 ↔ Y = 0#64) := fun h => by rw [h]
      exact (e (by simp [setReg])).trans hz
    · have := hkM 28 (by simp)
      simp [setReg] at this
      simp [setReg]
      rw [this, b28, h28]
    · have := hkM 29 (by simp)
      simp [setReg] at this
      simp [setReg]
      rw [this, b29, h29]
    · have := hkM 18 (by simp)
      simp [setReg] at this
      simp [setReg]
      rw [this, b18, h18]
    · exact esp.symm
    · have h0 := hy_limb 0 (by omega); have h1 := hy_limb 1 (by omega)
      have h2 := hy_limb 2 (by omega); have h3 := hy_limb 3 (by omega)
      simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at h0 h1 h2 h3 ⊢
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
      have hb := hbyM (nd - 1 - k) (by omega)
      rw [show b + 94 + pos - 1 - k = b + 94 + (pos - nd) + (nd - 1 - k) by omega, hb]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [Janus.Arm64.Memory.readLE_one, show b + 75 + (nd - 1 - k) = b + 75 + nd - 1 - k by omega, bdig k hk,
        Fv256.E.digit_mod y k 19 (by omega)]
    · have tr : ∀ {m1 m2 m3 : Memory}, MemFrame m1 m2 [(b - 344, b - 8), (b + 8, b + 94), (b + 94 + (pos - nd), b + 94 + pos), (b + 192, b + 376)] →
          MemFrame m2 m3 [(b - 344, b - 8), (b + 8, b + 94), (b + 94 + (pos - nd), b + 94 + pos), (b + 192, b + 376)] →
          MemFrame m1 m3 [(b - 344, b - 8), (b + 8, b + 94), (b + 94 + (pos - nd), b + 94 + pos), (b + 192, b + 376)] :=
        fun h h' => h.trans h' (fun a n h => ⟨h, h⟩)
      have wr : ∀ {m1 m2 : Memory} {a k v : Nat}, MemFrame m1 m2 [(b - 344, b - 8), (b + 8, b + 94), (b + 94 + (pos - nd), b + 94 + pos), (b + 192, b + 376)] →
          ((b - 344 ≤ a ∧ a + k ≤ b - 8) ∨ (b + 8 ≤ a ∧ a + k ≤ b + 94) ∨ (b + 94 + (pos - nd) ≤ a ∧ a + k ≤ b + 94 + pos) ∨ (b + 192 ≤ a ∧ a + k ≤ b + 376)) →
          MemFrame m1 (m2.writeLE a k v) [(b - 344, b - 8), (b + 8, b + 94), (b + 94 + (pos - nd), b + 94 + pos), (b + 192, b + 376)] := by
        intro m1 m2 a k v h hr
        rcases hr with hr | hr | hr | hr
        · exact h.writeLE v (List.mem_cons_self ..) hr.1 hr.2
        · exact h.writeLE v (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hr.1 hr.2
        · exact h.writeLE v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) hr.1 hr.2
        · exact h.writeLE v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))) hr.1 hr.2
      refine tr ?_ (tr (hfr.mono ?_) (tr ?_ (tr (bfr.mono ?_) (tr ?_ (hfrM2.mono ?_)))))
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
    · have hwaS : ∀ a n, b - 344 ≤ a → a + n ≤ b + 384 → sA.mem.accessible a n true = true := by
        intro a n h1 h2
        rw [bfr.accessible]
        simp only [Janus.Arm64.Memory.accessible_writeLE]
        exact accessible_sub hw1 (Or.inr rfl) h1 (by omega)
      refine TabsOK.frame ?_ hfrM2 ?_
      · repeat' first
          | exact btab
          | refine TabsOK.writeLE ?_ ?_ _
          | (simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hwaS _ _ (by omega) (by omega))
          | exact hwaS _ _ (by omega) (by omega)
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr
        simp only [Janus.Arm64.Memory.accessible_writeLE]
        exact hwaS _ _ (by omega) (by omega)
end Fv256.Arm64.Dec
