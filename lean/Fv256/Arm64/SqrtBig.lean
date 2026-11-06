import Fv256.Arm64.SqrtSmall
import Fv256.Arm64.UdivremFinal
import Fv256.Arm64.CodeIn
import Fv256.Arm64.ChainProg
import Fv256.SqrtMath
import Fv256.SqrtLimb
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecF
import Fv256.UtilF
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.Arm64.SqrtLimbA

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SqrtSum

set_option maxRecDepth 200000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ChainProg.program Fv256.Arm64.SqrtProg.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

abbrev headB : Nat := sqrtEntry + 0x1d4

/-- the head of the Newton loop of the 256-bit path: `z1` (limbs `a`) at `SP1+104`, `z2` (limbs `b`) at `SP1+72` -/
def BigInv (s0 : State) (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (z x : Nat) (S : State) : Prop :=
  S.pc = BitVec.ofNat 64 headB ∧ S.sp.toNat = s0.sp.toNat - 144 ∧ S.regs 18 = s0.regs 18 ∧ S.regs 28 = s0.regs 28 ∧
  S.regs 29 = s0.sp - 152#64 ∧
  S.mem.readLE (s0.sp.toNat - 40) 8 = a0 ∧ S.mem.readLE (s0.sp.toNat - 32) 8 = a1 ∧
  S.mem.readLE (s0.sp.toNat - 24) 8 = a2 ∧ S.mem.readLE (s0.sp.toNat - 16) 8 = a3 ∧
  S.mem.readLE (s0.sp.toNat - 72) 8 = b0 ∧ S.mem.readLE (s0.sp.toNat - 64) 8 = b1 ∧
  S.mem.readLE (s0.sp.toNat - 56) 8 = b2 ∧ S.mem.readLE (s0.sp.toNat - 48) 8 = b3 ∧
  S.mem.readLE (s0.sp.toNat - 144) 8 = (s0.regs 30).toNat ∧ S.mem.readLE (s0.sp.toNat - 152) 8 = (s0.regs 29).toNat ∧
  S.mem.readLE (s0.sp.toNat + 8) 8 = z ∧ S.mem.readLE (s0.sp.toNat + 16) 8 = x ∧
  a0 < 2 ^ 64 ∧ a1 < 2 ^ 64 ∧ a2 < 2 ^ 64 ∧ a3 < 2 ^ 64 ∧ b0 < 2 ^ 64 ∧ b1 < 2 ^ 64 ∧ b2 < 2 ^ 64 ∧ b3 < 2 ^ 64 ∧
  MemFrame s0.mem S.mem [(s0.sp.toNat - 488, s0.sp.toNat - 8), (s0.sp.toNat + 8, s0.sp.toNat + 24)]

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem big_loop (s0 : State) (X : Nat)
    (h30a : (s0.regs 30).toNat % 4 = 0) (h30b : (s0.regs 30).toNat < 2 ^ 56)
    (hal : s0.sp.toNat % 16 = 0) (hsp : 488 ≤ s0.sp.toNat) (hspb : s0.sp.toNat + 24 ≤ 2 ^ 48)
    (hwin : s0.mem.accessible (s0.sp.toNat - 488) (488 + 24) true = true)
    (hg1 : (s0.regs 28).toNat + 24 ≤ 2 ^ 48) (hg2 : s0.mem.accessible ((s0.regs 28).toNat + 16) 8 false = true)
    (hg3 : s0.mem.readLE ((s0.regs 28).toNat + 16) 8 + 448 < s0.sp.toNat)
    (hdg : Apart ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 488) 512)
    (hzb : (s0.regs 0).toNat + 32 ≤ 2 ^ 48) (hza : s0.mem.accessible (s0.regs 0).toNat 32 true = true)
    (hdz : Apart (s0.regs 0).toNat 32 (s0.sp.toNat - 488) 512)
    (hxb : (s0.regs 1).toNat + 32 ≤ 2 ^ 48) (hxa : s0.mem.accessible (s0.regs 1).toNat 32 false = true)
    (hdx : Apart (s0.regs 1).toNat 32 (s0.sp.toNat - 488) 512)
    (hX64 : 2 ^ 64 ≤ X) (hX256 : X < 2 ^ 256)
    (hXmem : s0.mem.readLE (s0.regs 1).toNat 32 = X) :
    ∀ A a0 a1 a2 a3 b0 b1 b2 b3 (S : State), A = a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 →
      BigInv s0 a0 a1 a2 a3 b0 b1 b2 b3 (s0.regs 0).toNat (s0.regs 1).toNat S →
      b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3 = X / A → 0 < A → A ≤ 2 ^ 128 → X < (A + 1) * (A + 1) →
      ReachesRet Fv256.Arm64.SqrtProg.program (s0.regs 30) S (PostSq s0) := by
  intro A
  induction A using Nat.strongRecOn with
  | _ A ih =>
    intro a0 a1 a2 a3 b0 b1 b2 b3 S hA hI hAB hApos hAle hXinv
    subst hA
    obtain ⟨hpc, hsp', r18, r28, r29, ma0, ma1, ma2, ma3, mb0, mb1, mb2, mb3, mret, mfp, mz, mx,
      la0, la1, la2, la3, lb0, lb1, lb2, lb3, hfr⟩ := hI
    simp only [headB, reduceSegAddr, Nat.reduceAdd] at hpc
    have hMa : S.mem.accessible (s0.sp.toNat - 488) (488 + 24) true = true := by rw [hfr.accessible]; exact hwin
    have hspb' : S.sp.toNat + 24 ≤ 2 ^ 48 := by omega
    have hspal' : S.sp.toNat % 16 = 0 := by omega
    have mret' : S.mem.readLE S.sp.toNat 8 = (s0.regs 30).toNat := by rw [hsp']; exact mret
    have mfp' : S.mem.readLE (S.sp.toNat - 8) 8 = (s0.regs 29).toNat := by
      rw [hsp', show s0.sp.toNat - 144 - 8 = s0.sp.toNat - 152 by omega]; exact mfp
    have hdzu : (s0.regs 0).toNat + 32 ≤ s0.sp.toNat - 488 ∨ s0.sp.toNat + 24 ≤ (s0.regs 0).toNat := by
      unfold Apart at hdz; omega
    have hdxu : (s0.regs 1).toNat + 32 ≤ s0.sp.toNat - 488 ∨ s0.sp.toNat + 24 ≤ (s0.regs 1).toNat := by
      unfold Apart at hdx; omega
    have hdgu : (s0.regs 28).toNat + 24 ≤ s0.sp.toNat - 488 ∨ s0.sp.toNat + 24 ≤ (s0.regs 28).toNat + 16 := by
      unfold Apart at hdg; omega
    have mz' : S.mem.readLE (S.sp.toNat + 152) 8 = (s0.regs 0).toNat := by
      rw [show S.sp.toNat + 152 = s0.sp.toNat + 8 by omega]; exact mz
    have mx' : S.mem.readLE (S.sp.toNat + 160) 8 = (s0.regs 1).toNat := by
      rw [show S.sp.toNat + 160 = s0.sp.toNat + 16 by omega]; exact mx
    have hza' : S.mem.accessible (s0.regs 0).toNat 32 true = true := by rw [hfr.accessible]; exact hza
    have hxa' : S.mem.accessible (s0.regs 1).toNat 32 false = true := by rw [hfr.accessible]; exact hxa
    have ma0' : S.mem.readLE (S.sp.toNat + 104) 8 = a0 := by rw [show S.sp.toNat + 104 = s0.sp.toNat - 40 by omega]; exact ma0
    have ma1' : S.mem.readLE (S.sp.toNat + 112) 8 = a1 := by rw [show S.sp.toNat + 112 = s0.sp.toNat - 32 by omega]; exact ma1
    have ma2' : S.mem.readLE (S.sp.toNat + 120) 8 = a2 := by rw [show S.sp.toNat + 120 = s0.sp.toNat - 24 by omega]; exact ma2
    have ma3' : S.mem.readLE (S.sp.toNat + 128) 8 = a3 := by rw [show S.sp.toNat + 128 = s0.sp.toNat - 16 by omega]; exact ma3
    have mb0' : S.mem.readLE (S.sp.toNat + 72) 8 = b0 := by rw [show S.sp.toNat + 72 = s0.sp.toNat - 72 by omega]; exact mb0
    have mb1' : S.mem.readLE (S.sp.toNat + 80) 8 = b1 := by rw [show S.sp.toNat + 80 = s0.sp.toNat - 64 by omega]; exact mb1
    have mb2' : S.mem.readLE (S.sp.toNat + 88) 8 = b2 := by rw [show S.sp.toNat + 88 = s0.sp.toNat - 56 by omega]; exact mb2
    have mb3' : S.mem.readLE (S.sp.toNat + 96) 8 = b3 := by rw [show S.sp.toNat + 96 = s0.sp.toNat - 48 by omega]; exact mb3
    have hlt := SqrtMath.no_overflow_256 X _ hApos hAle hXinv
    have hshr := Fv256.Arm64.SqrtLimbA.add_shr_arm a0 a1 a2 a3 b0 b1 b2 b3 la0 la1 la2 la3 lb0 lb1 lb2 lb3 (by omega)
    have hstep := SqrtMath.step_pos X _ hApos (by omega) hXinv
    unfold SqrtMath.step at hstep
    janus_run [r18, r28, r29, ma0', ma1', ma2', ma3', mb0', mb1', mb2', mb3', mret', mfp', mz', mx', Fv256.B.wv4_eq, Util.readLE_32]
      until [headB] calls [Janus.Contracts.EqHashModel.Summary.of_codeIn hcChain (Fv256.Arm64.UdivremFinal.udivrem_nil_L_final (L := 4) (by decide) (by decide))]
    · -- exit: z2' >= z1
      rename_i hcmp hr30b
      have hge := (Fv256.Arm64.SqrtLimbA.cmp_arm _ _ _ _ a0 a1 a2 a3 la0 la1 la2 la3).mp hcmp
      rw [Fv256.Arm64.SqrtLimbA.t3_eq] at hge
      have hstop : (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) ≤
          SqrtMath.step X (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) := by
        unfold SqrtMath.step; omega
      have hsq := SqrtMath.isSqrt_of_stop X _ hApos hXinv hstop
      unfold PostSq
      simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
      refine ⟨trivial, ?_, trivial, r18, r28, trivial, trivial, ?_, ?_⟩
      · apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        have := s0.sp.isLt
        omega
      · rw [hXmem]
        simp (disch := omega) only [Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          Janus.Arm64.Memory.readLE_writeLE_self]
        simp only [show (256 : Nat) ^ 8 = 2 ^ 64 by decide, Nat.mod_eq_of_lt la0, Nat.mod_eq_of_lt la1, Nat.mod_eq_of_lt la2,
          Nat.mod_eq_of_lt la3]
        exact hsq
      · janus_frame
    · -- continue
      rename_i ha lpc lsp l18 l28 l29 l30 lreg lwv hf
      have e72 : (S.sp + 72#64).toNat = S.sp.toNat + 72 := by
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have e104 : (S.sp + 104#64).toNat = S.sp.toNat + 104 := by
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      simp (config := { decide := true }) only [setReg_apply, ↓reduceIte, e72, e104] at hf lwv
      have hsumA : s'.mem.readLE (S.sp.toNat + 104) 8 + 2 ^ 64 * s'.mem.readLE (S.sp.toNat + 112) 8 +
          2 ^ 128 * s'.mem.readLE (S.sp.toNat + 120) 8 + 2 ^ 192 * s'.mem.readLE (S.sp.toNat + 128) 8 =
          ((a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3)) / 2 := by
        rw [hf.readLE _ _ (by simp [Outside]; omega), hf.readLE _ _ (by simp [Outside]; omega),
          hf.readLE _ _ (by simp [Outside]; omega), hf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        simp only [show (256 : Nat) ^ 8 = 2 ^ 64 by decide]
        simp (disch := first | exact BitVec.isLt _ | omega) only [Nat.mod_eq_of_lt]
        omega
      simp (config := { decide := true, failIfUnchanged := false }) only [setReg_apply, ↓reduceIte] at ha lpc lsp l18 l28 l29 l30 lreg
      have hfin : MemFrame s0.mem s'.mem [(s0.sp.toNat - 488, s0.sp.toNat - 8), (s0.sp.toNat + 8, s0.sp.toNat + 24)] := by
        janus_frame
      have key : ∀ p : Nat, S.sp.toNat - 8 ≤ p → (p + 8 ≤ S.sp.toNat + 8 ∨ S.sp.toNat + 136 ≤ p) →
          s'.mem.readLE p 8 = S.mem.readLE p 8 := by
        intro p h1 h2
        rw [hf.readLE p 8 (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      have lt64 : ∀ p, s'.mem.readLE p 8 < 2 ^ 64 := fun p => by
        have := Janus.Arm64.Memory.readLE_lt s'.mem p 8
        simpa using this
      have hxs : s'.mem.readLE (s0.regs 1).toNat 32 = X :=
        (hfin.readLE _ _ (by simp [Outside]; omega)).trans hXmem
      have hm32 : s'.mem.readLE (S.sp.toNat + 104) 32 =
          ((a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3)) / 2 := by
        rw [Util.readLE_32]
        have h := hsumA
        simp only [Nat.add_assoc, Nat.reduceAdd] at h ⊢
        exact h
      have lwv2 : s'.mem.readLE (S.sp.toNat + 72) 32 =
          s'.mem.readLE (s0.regs 1).toNat 32 / s'.mem.readLE (S.sp.toNat + 104) 32 := by
        rw [hf.readLE ((s0.regs 1).toNat) 32 (by simp [Outside]; omega),
          hf.readLE (S.sp.toNat + 104) 32 (by simp [Outside]; omega)]
        simp only [Fv256.B.wv4_eq] at lwv
        exact lwv
      have hsumA' : s'.mem.readLE (s0.sp.toNat - 40) 8 + 2 ^ 64 * s'.mem.readLE (s0.sp.toNat - 32) 8 +
          2 ^ 128 * s'.mem.readLE (s0.sp.toNat - 24) 8 + 2 ^ 192 * s'.mem.readLE (s0.sp.toNat - 16) 8 =
          ((a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3)) / 2 := by
        rw [show s0.sp.toNat - 40 = S.sp.toNat + 104 by omega, show s0.sp.toNat - 32 = S.sp.toNat + 112 by omega,
          show s0.sp.toNat - 24 = S.sp.toNat + 120 by omega, show s0.sp.toNat - 16 = S.sp.toNat + 128 by omega]
        exact hsumA
      have hb : s'.mem.readLE (s0.sp.toNat - 72) 8 + 2 ^ 64 * s'.mem.readLE (s0.sp.toNat - 64) 8 +
          2 ^ 128 * s'.mem.readLE (s0.sp.toNat - 56) 8 + 2 ^ 192 * s'.mem.readLE (s0.sp.toNat - 48) 8 =
          X / (((a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3)) / 2) := by
        have h2 := lwv2
        rw [hxs, hm32, Util.readLE_32] at h2
        simp only [Nat.add_assoc, Nat.reduceAdd] at h2
        rw [show s0.sp.toNat - 72 = S.sp.toNat + 72 by omega, show s0.sp.toNat - 64 = S.sp.toNat + 80 by omega,
          show s0.sp.toNat - 56 = S.sp.toNat + 88 by omega, show s0.sp.toNat - 48 = S.sp.toNat + 96 by omega]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        exact h2
      have hlt2 := mt (Fv256.Arm64.SqrtLimbA.cmp_arm _ _ _ _ a0 a1 a2 a3 la0 la1 la2 la3).mpr hbr
      rw [Fv256.Arm64.SqrtLimbA.t3_eq] at hlt2
      have hmlt : ((a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3)) / 2 <
          a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 := by omega
      have hmeq : ((a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3)) / 2 =
          SqrtMath.step X (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) := by
        unfold SqrtMath.step; rw [hAB]
      have hXm : X < (((a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3)) / 2 + 1) *
          (((a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3)) / 2 + 1) := by
        rw [hmeq]; exact SqrtMath.inv_step X _ hApos hXinv
      have hpos : 0 < ((a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3)) / 2 := by
        have := hstep
        rw [← hAB] at this
        exact this
      have hmret : s'.mem.readLE (s0.sp.toNat - 144) 8 = (s0.regs 30).toNat := by
        rw [show s0.sp.toNat - 144 = S.sp.toNat by omega, key _ (by omega) (by omega)]; exact mret'
      have hmfp : s'.mem.readLE (s0.sp.toNat - 152) 8 = (s0.regs 29).toNat := by
        rw [show s0.sp.toNat - 152 = S.sp.toNat - 8 by omega, key _ (by omega) (by omega)]; exact mfp'
      have hmz : s'.mem.readLE (s0.sp.toNat + 8) 8 = (s0.regs 0).toNat := by
        rw [show s0.sp.toNat + 8 = S.sp.toNat + 152 by omega, key _ (by omega) (by omega)]; exact mz'
      have hmx : s'.mem.readLE (s0.sp.toNat + 16) 8 = (s0.regs 1).toNat := by
        rw [show s0.sp.toNat + 16 = S.sp.toNat + 160 by omega, key _ (by omega) (by omega)]; exact mx'
      have hpc' : s'.pc = BitVec.ofNat 64 headB := by
        simp only [headB, reduceSegAddr, Nat.reduceAdd]; exact ha
      refine ih _ hmlt _ _ _ _ _ _ _ _ s' hsumA'.symm
        ⟨hpc', by rw [lsp]; exact hsp', l18.trans r18, l28.trans r28, l29.trans r29, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          hmret, hmfp, hmz, hmx, lt64 _, lt64 _, lt64 _, lt64 _, lt64 _, lt64 _, lt64 _, lt64 _, hfin⟩
        hb hpos (by omega) hXm

end Fv256.Arm64.SqrtSum
