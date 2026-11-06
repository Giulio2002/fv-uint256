import Fv256.Arm64.SfdFdB
import Fv256.Arm64.SegCompose

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdEnv Fv256.Arm64.SfdToError Fv256.Arm64.SfdPw Fv256.Arm64.SfdFd

namespace Fv256.Arm64.SfdFd

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- round `i > 0`: `tmp = d`, `tmp = tmp * 10^(19 i)` (`Mul`), `z += tmp` -/
theorem fd_midK (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State)
    (hn78 : nS.toNat ≤ 78) (hlo : lo + 4440 ≤ s.sp.toNat) (hhi : s.sp.toNat + 32 ≤ hi)
    (hal : s.sp.toNat % 16 = 0) (hs64 : s.sp.toNat + 32 < 2 ^ 64)
    (hzw : s.mem.accessible z.toNat 32 true = true) (hzb : z.toNat + 32 ≤ 2 ^ 48)
    (hzlh : z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat) (hzR : Outside z.toNat 32 R.rt ∨ InRanges z.toNat 32 L)
    (hzP : Outside z.toNat 32 R2.priv) (hzS : ∀ r ∈ staticRanges T, Outside r.1 (r.2 - r.1) [(z.toNat, z.toNat + 32)])
    (hzg : (s.regs 28).toNat + 16 + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 28).toNat + 16)
    (hMod : Mod R R2 T L) (hMult : MultOK z.toNat lo hi s.mem)
    (hfin : allDec (Fv256.C.bytesAt s.mem pS.toNat) 0 nS.toNat → decSum (Fv256.C.bytesAt s.mem pS.toNat) 0 nS.toNat < 2 ^ 256)
    (S : State) (i d : Nat) (hM : MidInv R R2 T b L lo hi z pS nS s i d S) (hi0 : i ≠ 0) :
    ReachesRet ((Fv256.Arm64.SfdToError.P).link impl) (BitVec.ofNat 64 m2) S (M2Inv R R2 T b L lo hi z pS nS s i) := by
  have hM' := hM
  obtain ⟨hpc, hi5, hrem, hd64, r0, r1, r4, hfl, rsp, r29, r28, r18, mi, mlen, mrem, mW, hfr, m1, m2', m3, m4, mtab, mval, hEnv, hfb, hdig, hd, hall, hK⟩ := hM'
  refine Fv256.Arm64.SegCompose.seg_trans (fd_to_mul impl R R2 T b L lo hi z pS nS s hn78 hlo hhi S i d hM hi0) ?_
  intro S3 hpc3 hq3
  obtain ⟨q0, q1, q2, q30, qsp, q29, q28, q18, qfl, qmem⟩ := hq3
  have hmult := hMult
  obtain ⟨hMa, hMo, hMk⟩ := hmult
  obtain ⟨hWa, hWb, hWv, hWo⟩ := hMk i (by omega) (by omega)
  have hsn : (s.sp - 88#64).toNat = s.sp.toNat - 88 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hWlt : s.mem.readLE (mulTab + 8 * i) 8 < 2 ^ 48 := by omega
  have hWn : (BitVec.ofNat 64 (s.mem.readLE (mulTab + 8 * i) 8)).toNat = s.mem.readLE (mulTab + 8 * i) 8 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hF3 : MemFrame s.mem S3.mem [(lo, hi), (z.toNat, z.toNat + 32)] := by
    rw [qmem]
    repeat' first
      | exact hfr
      | refine MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  have hWo' := hWo
  simp only [outside_cons, outside_nil, and_true] at hWo'
  obtain ⟨hWo1, hWo2⟩ := hWo'
  have hS3acc : ∀ a n w, S3.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hF3.accessible a n w
  refine ReachesRet.call (Fv256.Arm64.SfdMul.mul_sum impl (s.sp - 88#64) (s.sp - 88#64) (BitVec.ofNat 64 (s.mem.readLE (mulTab + 8 * i) 8))) hpc3 ?pre ?cont
  case pre =>
    unfold Fv256.Arm64.SfdMul.MulPre
    have hEnv' := hEnv
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
    have haccS3 : ∀ a n, lo ≤ a → a + n ≤ hi → S3.mem.accessible a n true = true := by
      intro a n h1 h2
      rw [hS3acc, ← hfr.accessible]
      exact Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
    refine ⟨?_, ?_, q0, q1, q2, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, Or.inl rfl, ?_, ?_⟩
    · rw [q30]; decide
    · rw [q30]; decide
    · rw [hsn]; exact haccS3 _ _ (by omega) (by omega)
    · rw [hsn]; omega
    · rw [hsn]; exact Arm64.Memory.accessible_weaken _ (haccS3 (s.sp.toNat - 88) 32 (by omega) (by omega))
    · rw [hsn]; omega
    · rw [hWn, hS3acc]; exact hWa
    · rw [hWn]; omega
    · right; simp only [Janus.Spec.Disjoint32, Janus.Spec.Disjoint, hsn, hWn]; omega
    · right; simp only [Janus.Spec.Disjoint32, Janus.Spec.Disjoint, hsn, hWn]; omega
  case cont =>
    intro S'' hpc'' hpost
    obtain ⟨p1, p29, p28, p18, p0, pval, pfr⟩ := hpost
    have hE' := hEnv
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hE'
    have hsp3 : S3.sp = s.sp - 160#64 := qsp
    have hF'' : MemFrame S3.mem S''.mem [(lo, hi), (z.toNat, z.toNat + 32)] := pfr.mono (by
      intro a n h
      simp only [outside_cons, outside_nil, and_true] at h ⊢
      rw [hsn]; omega)
    have hFs'' : MemFrame s.mem S''.mem [(lo, hi), (z.toNat, z.toNat + 32)] := hF3.trans hF'' (by
      intro a n h
      simp only [outside_cons, outside_nil, and_true] at h ⊢
      omega)
    have hS''acc : ∀ a n w, S''.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hFs''.accessible a n w
    have hrd : ∀ a, (a + 8 ≤ s.sp.toNat - 88 ∨ s.sp.toNat - 56 ≤ a) → S''.mem.readLE a 8 = S.mem.readLE a 8 := by
      intro a ha
      rw [pfr.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; rw [hsn]; omega), qmem]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have haccs : S''.mem.accessible (s.sp.toNat - 168) 200 true = true := by
      rw [hS''acc, ← hfr.accessible]
      exact Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
    have hzacc : S''.mem.accessible z.toNat 32 true = true := by rw [hS''acc]; exact hzw
    have hadd := fd_add impl s S'' z nS i lo hi hlo hhi hzb hzlh hn78 hrem (by rw [hpc'', q30]) (by rw [p1, qsp])
      (by rw [p0]) (by rw [hrd _ (by omega)]; exact m3) (by rw [hrd _ (by omega)]; exact mrem) (by rw [hrd _ (by omega)]; exact mi)
      hal hs64 haccs hzacc
    refine Fv256.Arm64.SegCompose.seg_mono hadd ?_
    intro S4 hq4
    obtain ⟨g1, g5, g2, g4, gfl, gsp, g29, g28, g18, gfr, gval⟩ := hq4
    have hle : nS - BitVec.ofNat 64 (19 * i) = BitVec.ofNat 64 (nS.toNat - 19 * i) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := nS.isLt; omega
    have hrd4 : ∀ a, (a + 8 ≤ s.sp.toNat - 88 ∨ s.sp.toNat - 56 ≤ a) → (a + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ a) →
        S4.mem.readLE a 8 = S.mem.readLE a 8 := by
      intro a h1 h2
      rw [gfr.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)]
      exact hrd a h1
    have hFS : MemFrame S.mem S3.mem [(lo, hi), (z.toNat, z.toNat + 32)] := by
      rw [qmem]
      repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
    have hG : MemFrame S''.mem S4.mem [(lo, hi), (z.toNat, z.toNat + 32)] :=
      gfr.mono (by intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    have hFS'' : MemFrame S.mem S''.mem [(lo, hi), (z.toNat, z.toNat + 32)] :=
      hFS.trans hF'' (by intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    have hFS4 : MemFrame S.mem S4.mem [(lo, hi), (z.toNat, z.toNat + 32)] :=
      hFS''.trans hG
        (by intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    have hFs4 : MemFrame s.mem S4.mem [(lo, hi), (z.toNat, z.toNat + 32)] :=
      hFs''.trans hG
        (by intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    have hzo : z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat := hzlh
    unfold M2Inv
    refine ⟨g1, hi5, hrem, g5, g2, ?r4, ?fl, ?sp, ?r29, ?r28, ?r18, ?mlen, hFs4, ?x30, ?x29, ?xz, ?xp, ?tab, ?val, ?env, ?fb, ?hall, ?keep⟩
    case r4 => rw [g4, hle]
    case fl => rw [gfl, hle]
    case sp => rw [gsp, p1, qsp]
    case r29 => rw [g29, p29, q29, r29]
    case r28 => rw [g28, p28, q28, r28]
    case r18 => rw [g18, p18, q18, r18]
    case mlen => rw [hrd4 (s.sp.toNat - 96) (by omega) (by omega)]; exact mlen
    case x30 => rw [hrd4 (s.sp.toNat - 160) (by omega) (by omega)]; exact m1
    case x29 => rw [hrd4 (s.sp.toNat - 168) (by omega) (by omega)]; exact m2'
    case xz => rw [hrd4 (s.sp.toNat + 8) (by omega) (by omega)]; exact m3
    case xp => rw [hrd4 (s.sp.toNat + 16) (by omega) (by omega)]; exact m4
    case tab => intro k hk; rw [hrd4 (s.sp.toNat - 48 + 8 * k) (by omega) (by omega)]; exact mtab k hk
    case env =>
      refine Env.frame hMod.1 hEnv ?_ ?_ hFS4 hzR hzP hzS (by rw [r28]; exact hzg)
      · rw [gsp, p1, qsp]; show lo ≤ (s.sp - 160#64).toNat ∧ (s.sp - 160#64).toNat + 8 ≤ hi ∧ (s.sp - 160#64).toNat % 16 = 0
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; refine ⟨by omega, by omega, by omega⟩
      · rw [g28, p28, q28, r28]
    case fb => rw [hfb]; exact fb_good _ _ _ hi5 hrem (by rw [chunk_hi]; exact hdig)
    case hall => have := hdig; rw [chunk_lo_eq] at this; exact allDec_join this hall
    case keep =>
      unfold Keep
      refine ⟨?_, ?_⟩
      · rw [hrd4 (s.sp.toNat - 8) (by omega) (by omega)]; exact hK.1
      · rw [hrd4 s.sp.toNat (by omega) (by omega)]; exact hK.2
    case val =>
      have hv1 : Janus.Spec.val256 S''.mem z.toNat = accV (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat i := by
        rw [← mval]; unfold Janus.Spec.val256
        rw [pfr.readLE z.toNat 32 (by simp only [outside_cons, outside_nil, and_true]; rw [hsn]; omega), qmem]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      have hv3 : Janus.Spec.val256 S3.mem (s.sp.toNat - 88) = d := by
        unfold Janus.Spec.val256
        rw [qmem, Util.readLE_32]
        have e1 : s.sp.toNat - 88 + 8 = s.sp.toNat - 80 := by omega
        have e2 : s.sp.toNat - 88 + 16 = s.sp.toNat - 72 := by omega
        have e3 : s.sp.toNat - 88 + 24 = s.sp.toNat - 64 := by omega
        rw [e1, e2, e3]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.zero_mod]
        rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt hd64]; omega
      have hv4 : Janus.Spec.val256 S3.mem (s.mem.readLE (mulTab + 8 * i) 8) = 10 ^ (19 * i) := by
        rw [← hWv]; unfold Janus.Spec.val256
        exact hF3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
      have hv5 : Janus.Spec.val256 S''.mem (s.sp.toNat - 88) = (d * 10 ^ (19 * i)) % 2 ^ 256 := by
        have := pval
        rw [hsn, hWn, hv3, hv4] at this
        exact this
      rw [gval, hv1, hv5]
      have hsucc := accV_succ (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat i hrem
      rw [← chunk_lo_eq, ← hd] at hsucc
      have hall' : allDec (Fv256.C.bytesAt s.mem pS.toNat) (nS.toNat - 19 * (i + 1)) nS.toNat := by
        have := hdig; rw [chunk_lo_eq] at this; exact allDec_join this hall
      have hlt := accV_lt (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat (i + 1) hn78 (by omega) hall' hfin
      rw [hsucc] at hlt ⊢
      rw [Nat.mod_eq_of_lt (by omega)]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega

end Fv256.Arm64.SfdFd
