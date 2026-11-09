import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Amd64.SqrtLibBase
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Common.SqrtMath
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Amd64.SqrtBigL
import Fv256.Proofs.Common.SqrtLimb

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SqrtLib

abbrev headB : Nat := Fv256.Amd64.SqrtLib.sqrtEntry + 0x205

def BigInv (s0 : State) (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (z x : BitVec 64) (S : State) : Prop :=
  S.rip = BitVec.ofNat 64 headB ∧ S.regs 4 = s0.regs 4 - 136#64 ∧ S.regs 5 = s0.regs 4 - 8#64 ∧ S.regs 14 = s0.regs 14 ∧
  S.xmm 15 = 0 ∧ S.df = s0.df ∧ S.mxcsr = s0.mxcsr ∧
  S.mem.readLE ((s0.regs 4).toNat - 40) 8 = a0 ∧ S.mem.readLE ((s0.regs 4).toNat - 32) 8 = a1 ∧
  S.mem.readLE ((s0.regs 4).toNat - 24) 8 = a2 ∧ S.mem.readLE ((s0.regs 4).toNat - 16) 8 = a3 ∧
  S.mem.readLE ((s0.regs 4).toNat - 72) 8 = b0 ∧ S.mem.readLE ((s0.regs 4).toNat - 64) 8 = b1 ∧
  S.mem.readLE ((s0.regs 4).toNat - 56) 8 = b2 ∧ S.mem.readLE ((s0.regs 4).toNat - 48) 8 = b3 ∧
  S.mem.readLE (s0.regs 4).toNat 8 = s0.mem.readLE (s0.regs 4).toNat 8 ∧ S.mem.readLE ((s0.regs 4).toNat - 8) 8 = (s0.regs 5).toNat ∧
  S.mem.readLE ((s0.regs 4).toNat + 8) 8 = z.toNat ∧ S.mem.readLE ((s0.regs 4).toNat + 16) 8 = x.toNat ∧
  a0 < 2 ^ 64 ∧ a1 < 2 ^ 64 ∧ a2 < 2 ^ 64 ∧ a3 < 2 ^ 64 ∧ b0 < 2 ^ 64 ∧ b1 < 2 ^ 64 ∧ b2 < 2 ^ 64 ∧ b3 < 2 ^ 64 ∧
  S.mem.accessible ((s0.regs 4).toNat - 0x1f0) (0x1f0 + 0x18) true = true ∧
  S.mem.accessible x.toNat 32 false = true ∧ S.mem.accessible z.toNat 32 true = true ∧ z.toNat + 32 ≤ 2 ^ 48 ∧ x.toNat + 32 ≤ 2 ^ 48 ∧
  MemFrame s0.mem S.mem [((s0.regs 4).toNat - 0x1f0, (s0.regs 4).toNat + 0x18)]

theorem sub144 (a : BitVec 64) : a - 144#64 + 8#64 = a - 136#64 := by bv_omega

theorem retAddrOf_push (s : State) (m : Janus.Arm64.Memory) (a v : Nat) (ha : (s.regs 4).toNat = a)
    (hm : s.mem = m.writeLE a 8 v) (hv : v < 2 ^ 64) : retAddrOf s = BitVec.ofNat 64 v := by
  unfold retAddrOf
  rw [ha, hm, Janus.Arm64.Memory.readLE_writeLE_self]
  have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  rw [this, Nat.mod_eq_of_lt hv]

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem big_loop (s0 : State) (X : Nat) (z x : BitVec 64) (Q : State → Prop)
    (hX64 : 2 ^ 64 ≤ X) (hX256 : X < 2 ^ 256)
    (hret47 : s0.mem.readLE (s0.regs 4).toNat 8 < 2 ^ 47)
    (hdz : z.toNat + 32 ≤ (s0.regs 4).toNat - 0x1f0 ∨ (s0.regs 4).toNat + 0x18 ≤ z.toNat)
    (hdx : x.toNat + 32 ≤ (s0.regs 4).toNat - 0x1f0 ∨ (s0.regs 4).toNat + 0x18 ≤ x.toNat)
    (hdg : (s0.regs 14).toNat + 24 ≤ (s0.regs 4).toNat - 0x1f0 ∨ (s0.regs 4).toNat + 0x18 ≤ (s0.regs 14).toNat + 16)
    (hgb : s0.mem.readLE ((s0.regs 14).toNat + 16) 8 + 0x200 < (s0.regs 4).toNat)
    (hnw2 : (s0.regs 14).toNat + 16 + 8 ≤ 2 ^ 48)
    (hgr : s0.mem.accessible ((s0.regs 14).toNat + 16) 8 false = true)
    (hsp : 0x280 ≤ (s0.regs 4).toNat) (hsp48 : (s0.regs 4).toNat + 0x18 ≤ 2 ^ 48)
    (hex : ∀ r (S' : State), SqrtMath.IsSqrt X r →
        S'.regs 0 = z → S'.regs 4 = s0.regs 4 + 8#64 → S'.regs 5 = s0.regs 5 → S'.regs 14 = s0.regs 14 → S'.xmm 15 = 0 →
        S'.df = s0.df → S'.mxcsr = s0.mxcsr → S'.mem.readLE z.toNat 32 = r →
        MemFrame s0.mem S'.mem [(z.toNat, z.toNat + 32), ((s0.regs 4).toNat - 0x1f0, (s0.regs 4).toNat + 0x18)] → Q S') :
    ∀ A a0 a1 a2 a3 b0 b1 b2 b3 (S : State), A = a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 →
      BigInv s0 a0 a1 a2 a3 b0 b1 b2 b3 z x S →
      b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3 = X / A → 0 < A → A ≤ 2 ^ 128 → X < (A + 1) * (A + 1) →
      S.mem.readLE x.toNat 32 = X →
      ReachesRet Fv256.SqrtProg.program (retAddrOf s0) S Q := by
  intro A
  induction A using Nat.strongRecOn with
  | _ A ih =>
    intro a0 a1 a2 a3 b0 b1 b2 b3 S hA hI hAB hApos hAle hXinv hXmem
    subst hA
    obtain ⟨hpc, r4, r5, r14, x15, hdf, hmx, ma0, ma1, ma2, ma3, mb0, mb1, mb2, mb3, mret, msav, mz, mx,
      la0, la1, la2, la3, lb0, lb1, lb2, lb3, hwin, hxacc, hzacc, hzw, hxw, hfr⟩ := hI
    have ez8 : (z.toNat + 8) % 18446744073709551616 = z.toNat + 8 := by omega
    have ez16 : (z.toNat + 16) % 18446744073709551616 = z.toNat + 16 := by omega
    have ez24 : (z.toNat + 24) % 18446744073709551616 = z.toNat + 24 := by omega
    have hlt := SqrtMath.no_overflow_256 X _ hApos hAle hXinv
    have hadd := SqrtLimb.add_shr a0 a1 a2 a3 b0 b1 b2 b3 la0 la1 la2 la3 lb0 lb1 lb2 lb3 (by omega)
    have hadd' := SqrtLimb.add_shr' a0 a1 a2 a3 b0 b1 b2 b3 la0 la1 la2 la3 lb0 lb1 lb2 lb3 (by omega)
    have hstep := SqrtMath.step_pos X _ hApos (by omega) hXinv
    unfold SqrtMath.step at hstep
    have hcode : headB + 0x100 < 2 ^ 47 := by decide
    janus64_run [r4, r5, r14, x15, hdf, hmx, ma0, ma1, ma2, ma3, mb0, mb1, mb2, mb3, mret, msav, mz, mx, ez8, ez16, ez24,
        Fv256.B.wv4_eq, Util.readLE_32, Fv256.B.borrow_zero_iff] until [headB]
      calls [Fv256.CodeIn.lib_summary hcChain Fv256.Amd64.UdivremL.udivrem_nil]
    · rename_i hge
      have hstop : (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) ≤ SqrtMath.step X (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) := by
        unfold SqrtMath.step; omega
      have hsq := SqrtMath.isSqrt_of_stop X _ hApos hXinv hstop
      refine hex _ _ hsq ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · simp [setRegF]
      · simp [setRegF, r4]
      · simp [setRegF, r5]
      · simp [setRegF, r14]
      · simp [setRegF, x15]
      · simp
      · simp
      · simp (disch := omega) only [Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]
        have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
        rw [h8, Nat.mod_eq_of_lt la0, Nat.mod_eq_of_lt la1, Nat.mod_eq_of_lt la2, Nat.mod_eq_of_lt la3]
      · janus_frame
    · rename_i R' fl' X' M' kr hq hF
      have hsumA : M'.readLE ((s0.regs 4).toNat - 40) 8 + 2 ^ 64 * M'.readLE ((s0.regs 4).toNat - 40 + 8) 8 +
          2 ^ 128 * M'.readLE ((s0.regs 4).toNat - 40 + 16) 8 + 2 ^ 192 * M'.readLE ((s0.regs 4).toNat - 40 + 24) 8 =
          ((a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3)) / 2 := by
        rw [hF.readLE _ _ (by simp [Outside]; omega), hF.readLE _ _ (by simp [Outside]; omega),
          hF.readLE _ _ (by simp [Outside]; omega), hF.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]
        have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
        have e1 : (s0.regs 4).toNat - 40 + 8 - ((s0.regs 4).toNat - 32) = 0 := by omega
        have e2 : (s0.regs 4).toNat - 40 + 16 - ((s0.regs 4).toNat - 24) = 0 := by omega
        have e3 : (s0.regs 4).toNat - 40 + 24 - ((s0.regs 4).toNat - 16) = 0 := by omega
        simp only [e1, e2, e3, Nat.pow_zero, Nat.div_one, h8, BitVec.toNat_mod_cancel]
        omega
      have hX0 : s0.mem.readLE x.toNat 8 + 18446744073709551616 * s0.mem.readLE (x.toNat + 8) 8 +
          340282366920938463463374607431768211456 * s0.mem.readLE (x.toNat + 16) 8 +
          6277101735386680763835789423207666416102355444464034512896 * s0.mem.readLE (x.toNat + 24) 8 = X := by
        rw [← hXmem, Util.readLE_32, hfr.readLE _ _ (by simp [Outside]; omega), hfr.readLE _ _ (by simp [Outside]; omega),
          hfr.readLE _ _ (by simp [Outside]; omega), hfr.readLE _ _ (by simp [Outside]; omega)]
      have key : ∀ X0 D c : Nat, D = c → X0 / D = X0 / c := fun X0 D c h => by rw [h]
      have hq2 := hq
      have f1 : (s0.regs 4).toNat - 72 + 8 = (s0.regs 4).toNat - 64 := by omega
      have f2 : (s0.regs 4).toNat - 72 + 16 = (s0.regs 4).toNat - 56 := by omega
      have f3 : (s0.regs 4).toNat - 72 + 24 = (s0.regs 4).toNat - 48 := by omega
      simp only [f1, f2, f3, hX0] at hq2
      rw [key _ _ ((a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3)) / 2) (by omega)] at hq2
      have hs144 : (s0.regs 4 - 144#64).toNat = (s0.regs 4).toNat - 144 := by
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      have g1 : (s0.regs 4).toNat - 40 + 8 = (s0.regs 4).toNat - 32 := by omega
      have g2 : (s0.regs 4).toNat - 40 + 16 = (s0.regs 4).toNat - 24 := by omega
      have g3 : (s0.regs 4).toNat - 40 + 24 = (s0.regs 4).toNat - 16 := by omega
      simp only [g1, g2, g3] at hsumA
      have hlt' : M'.readLE ((s0.regs 4).toNat - 40) 8 + 2 ^ 64 * M'.readLE ((s0.regs 4).toNat - 32) 8 +
          2 ^ 128 * M'.readLE ((s0.regs 4).toNat - 24) 8 + 2 ^ 192 * M'.readLE ((s0.regs 4).toNat - 16) 8 <
          a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 := by omega
      have hinv1 := SqrtMath.inv_step X _ hApos hXinv
      unfold SqrtMath.step at hinv1
      refine ih _ hlt' (M'.readLE ((s0.regs 4).toNat - 40) 8) (M'.readLE ((s0.regs 4).toNat - 32) 8)
        (M'.readLE ((s0.regs 4).toNat - 24) 8) (M'.readLE ((s0.regs 4).toNat - 16) 8)
        (M'.readLE ((s0.regs 4).toNat - 72) 8) (M'.readLE ((s0.regs 4).toNat - 64) 8)
        (M'.readLE ((s0.regs 4).toNat - 56) 8) (M'.readLE ((s0.regs 4).toNat - 48) 8) _ rfl ?inv ?hABn ?hposn ?hlen ?hXinvn ?hXm
      case hABn => rw [hsumA]; exact hq2
      case hposn => omega
      case hlen => omega
      case hXinvn => rw [hsumA, hAB]; exact hinv1
      case inv =>
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_,
          Util.readLE8_lt M' _, Util.readLE8_lt M' _, Util.readLE8_lt M' _, Util.readLE8_lt M' _,
          Util.readLE8_lt M' _, Util.readLE8_lt M' _, Util.readLE8_lt M' _, Util.readLE8_lt M' _, ?_, ?_, ?_, hzw, hxw, ?_⟩
        · exact (retAddrOf_push _ _ ((s0.regs 4).toNat - 144) 4957573 (by simp [setRegF, hs144]) rfl (by decide)).trans (by decide)
        · first | (simp [setRegF, r4]; done) | (simp [setRegF, r4, sub144]; done)
        · simp [setRegF, r5]; done
        · simp [setRegF, r14]; done
        · simp [setRegF, x15]; done
        · simp; done
        · simp; done
        · rw [hF.readLE _ _ (by simp [Outside]; omega)]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; exact mret
        · rw [hF.readLE _ _ (by simp [Outside]; omega)]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; exact msav
        · rw [hF.readLE _ _ (by simp [Outside]; omega)]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; exact mz
        · rw [hF.readLE _ _ (by simp [Outside]; omega)]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; exact mx
        · rw [hF.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hwin
        · rw [hF.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hxacc
        · rw [hF.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hzacc
        · refine MemFrame.trans (rs := [((s0.regs 4).toNat - 0x1f0, (s0.regs 4).toNat + 0x18)])
              (rs' := [((s0.regs 4).toNat - 0x1f0, (s0.regs 4).toNat + 0x18)]) hfr
              (MemFrame.trans (rs := [((s0.regs 4).toNat - 0x1f0, (s0.regs 4).toNat + 0x18)])
                (rs'' := [((s0.regs 4).toNat - 0x1f0, (s0.regs 4).toNat + 0x18)]) ?A hF ?sub1) ?sub2
          · repeat' (first | exact MemFrame.refl _ _ | refine MemFrame.writeLE_inRanges ?_ _ ⟨((s0.regs 4).toNat - 0x1f0, (s0.regs 4).toNat + 0x18), List.mem_cons_self .., by omega, by omega⟩)
          · intro a n h; simp [Outside] at h ⊢; omega
          · intro a n h; simp [Outside] at h ⊢; omega
      case hXm =>
        have hXm2 := hXmem
        rw [Util.readLE_32] at hXm2
        rw [Util.readLE_32, hF.readLE _ _ (by simp [Outside]; omega), hF.readLE _ _ (by simp [Outside]; omega),
          hF.readLE _ _ (by simp [Outside]; omega), hF.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
          Janus.Arm64.Memory.readLE_writeLE_inside]
        exact hXm2

end Fv256.Amd64.SqrtLib
