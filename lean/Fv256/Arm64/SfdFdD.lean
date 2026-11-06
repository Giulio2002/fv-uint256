import Fv256.Arm64.SfdFdC
import Fv256.Arm64.SfdFdMid

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdEnv Fv256.Arm64.SfdToError Fv256.Arm64.SfdPw Fv256.Arm64.SfdFd

namespace Fv256.Arm64.SfdFd

theorem TeObj.congr {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {fp fl sp sl : BitVec 64} {s1 s0 s' s'' : State} {q t : Nat}
    (h : TeObj R b L fp fl sp sl s1 s' q t) (h28 : s1.regs 28 = s0.regs 28)
    (he : s1.mem.readLE strconvErrSyntax 8 = s0.mem.readLE strconvErrSyntax 8)
    (he2 : s1.mem.readLE (strconvErrSyntax + 8) 8 = s0.mem.readLE (strconvErrSyntax + 8) 8)
    (hb : ∀ k, k < sl.toNat → s1.mem.readLE (sp.toNat + k) 1 = s0.mem.readLE (sp.toNat + k) 1)
    (hm : s''.mem = s'.mem) : TeObj R b L fp fl sp sl s0 s'' q t := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12⟩ := h
  unfold TeObj
  rw [hm]
  refine ⟨o1, o2, o3, o4, o5, o6, o7, o8, ?_, ?_, ?_, ?_⟩
  · rw [o9, he]
  · rw [o10, he2]
  · intro k hk; rw [o11 k hk, hb k hk]
  · rw [← h28]; exact o12

theorem out_sub (x k lo hi p n : Nat) (h : p + n ≤ lo ∨ hi ≤ p) (h1 : p ≤ x) (h2 : x + k ≤ p + n) :
    x + k ≤ lo ∨ hi ≤ x := by omega

theorem win_sub (a n lo hi lo' hi' : Nat) (h : a + n ≤ lo ∨ hi ≤ a) (h1 : lo ≤ lo') (h2 : hi' ≤ hi) :
    a + n ≤ lo' ∨ hi' ≤ a := by omega

theorem bvo (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- after `ParseUint` returned (either call site): the digits case reaches the merge point and continues with `hcont`;
the error case returns `(X1, X2)` -/
theorem fd_post_call (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State)
    (hpre : FdPre R R2 T b L lo hi z pS nS s)
    (S : State) (i : Nat) (hI : FdInv R R2 T b L lo hi z pS nS s i S) (hi5 : i < 5) (hrem : 19 * i < nS.toNat)
    (clo : Nat) (hclo : clo = (chunkBounds nS.toNat 0 i).1) (p len : BitVec 64)
    (hp : p = BitVec.ofNat 64 (pS.toNat + clo)) (hl : len = BitVec.ofNat 64 (nS.toNat - 19 * i - clo))
    (RA : Nat) (hRA : RA = 756796 ∨ RA = 756828) (S1 : State) (hS1 : PwCtx s S i nS RA S1)
    (S' : State) (hpost : PwPost R R2 T b L (s.sp.toNat - 4440) (s.sp.toNat - 112) p len S1 S')
    (hpc' : S'.pc = S1.regs 30)
    (hcont : ∀ (S2 : State) (d : Nat), MidInv R R2 T b L lo hi z pS nS s i d S2 →
      ReachesRet ((Fv256.Arm64.SfdToError.P).link impl) (s.regs 30) S2 (FdPost R R2 T b L lo hi z pS nS s)) :
    ReachesRet ((Fv256.Arm64.SfdToError.P).link impl) (s.regs 30) S' (FdPost R R2 T b L lo hi z pS nS s) := by
  obtain ⟨hl1, hl2, h0, h1, h2, hn78, hMod, hEnv0, hlo, hhi, hMult, hEOF, hEOFo, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA, hfin⟩ := hpre
  have hI' := hI
  obtain ⟨hpc, hi5', r0, r1, r3, r2, r4, rsp, r29, r28, r18, hfr, m1, m2', m3, m4, mtab, mval, hEnvS, hfb, hall⟩ := hI'
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hS1
  obtain ⟨k1, k29, k28, k18, kfp, klr, hcase⟩ := hpost
  have hspS : S.sp.toNat = s.sp.toNat - 160 := by rw [rsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsp1 : S1.sp.toNat = s.sp.toNat - 160 := by rw [c2]; exact hspS
  have hF1 : MemFrame S.mem S1.mem [(lo, hi)] := by
    rw [c1]
    repeat' first
      | exact MemFrame.refl _ _
      | refine MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  have hF1' : MemFrame S.mem S1.mem [(lo, hi), (z.toNat, z.toNat + 32)] :=
    hF1.mono (by intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
  have hFs1 : MemFrame s.mem S1.mem [(lo, hi), (z.toNat, z.toNat + 32)] :=
    hfr.trans hF1' (by intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
  have hS1rd : ∀ a, (a + 8 ≤ s.sp.toNat - 112 ∨ s.sp.toNat - 48 ≤ a) → S1.mem.readLE a 8 = S.mem.readLE a 8 := by
    intro a ha
    rw [c1]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hbn : (nS.toNat - 19 * i - clo) ≤ 19 := by rw [hclo, chunk_lo_eq]; omega
  have hbn1 : 1 ≤ nS.toNat - 19 * i - clo := by rw [hclo, chunk_lo_eq]; omega
  have hpn : p.toNat = pS.toNat + clo := by rw [hp, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hclo; rw [chunk_lo_eq] at this; omega)
  have hln : len.toNat = nS.toNat - 19 * i - clo := by rw [hl, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rcases hcase with ⟨hA, hv, hz1, hz2, hE', hfrOk⟩ | ⟨hA, hz0, ⟨q, t, hz3, hz2, hobj⟩, hfrE⟩
  · -- digits
    have hr_sp : S'.sp.toNat = s.sp.toNat - 160 := by rw [k1]; exact hsp1
    have hFo : MemFrame S1.mem S'.mem [(s.sp.toNat - 4440, s.sp.toNat - 112)] := hfrOk
    have hbyt : ∀ k, k < nS.toNat - 19 * i - clo → Fv256.C.bytesAt S1.mem (pS.toNat + clo) k =
        Fv256.C.bytesAt s.mem pS.toNat (clo + k) := by
      intro k hk; unfold Fv256.C.bytesAt
      rw [hFs1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; rw [Nat.add_assoc]
    rw [hpn, hln] at hA hv
    have hA' := (chunk_allDec_iff (Fv256.C.bytesAt s.mem pS.toNat) (Fv256.C.bytesAt S1.mem (pS.toNat + clo)) clo
      (nS.toNat - 19 * i - clo) hbyt).1 hA
    have hdig : allDec (Fv256.C.bytesAt s.mem pS.toNat) clo (nS.toNat - 19 * i) := by
      have e : clo + (nS.toNat - 19 * i - clo) = nS.toNat - 19 * i := by omega
      rw [e] at hA'; exact hA'
    have hdv : (S'.regs 0).toNat = decSum (Fv256.C.bytesAt s.mem pS.toNat) clo (nS.toNat - 19 * i - clo) := by
      rw [hv]; exact chunk_decSum _ _ _ _ hbyt
    have hEnvS' := hEnvS
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnvS'
    have hacc : S'.mem.accessible (S'.sp.toNat + 48) 8 false = true := by
      rw [hFo.accessible, hF1.accessible]
      exact Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ e5 (by omega) (by omega))
    have hr : S'.mem.readLE (S'.sp.toNat + 48) 8 = nS.toNat - 19 * i := by
      have ea : S'.sp.toNat + 48 = s.sp.toNat - 112 := by omega
      rw [ea, hFo.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), c1]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
      rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; have := nS.isLt; simp only [Nat.reducePow] at this; omega
    have hsp64 : S'.sp.toNat + 48 < 2 ^ 64 := by omega
    have hal : S'.sp.toNat % 16 = 0 := by rw [hr_sp]; omega
    refine Fv256.Arm64.SegCompose.seg_trans (fd_ret_to_mid impl S' s.sp.toNat (nS.toNat - 19 * i) RA hRA (by rw [hpc', c6]) hr_sp hacc hr hsp64 hal) ?_
    intro S2 hpc2 hq2
    obtain ⟨q1, q2, q3, q4, q5, qr2, q6, q7, q8, q9, q10⟩ := hq2
    have hle : nS - BitVec.ofNat 64 (19 * i) = BitVec.ofNat 64 (nS.toNat - 19 * i) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := nS.isLt; omega
    have hFo1 : MemFrame S1.mem S'.mem [(lo, hi)] :=
      hFo.mono (by intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    have hFo2 : MemFrame S1.mem S'.mem [(lo, hi), (z.toNat, z.toNat + 32)] :=
      hFo.mono (by intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    have hFS' : MemFrame S.mem S'.mem [(lo, hi)] :=
      hF1.trans hFo1 (by intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    have hFs' : MemFrame s.mem S'.mem [(lo, hi), (z.toNat, z.toNat + 32)] :=
      hFs1.trans hFo2 (by intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    have hrdo : ∀ a, (s.sp.toNat - 112 ≤ a) → (a + 8 ≤ s.sp.toNat - 112 ∨ s.sp.toNat - 48 ≤ a ∨ True) →
        S'.mem.readLE a 8 = S1.mem.readLE a 8 := by
      intro a h1 _
      sorry
    have hrS' : ∀ a, s.sp.toNat - 112 ≤ a → S2.mem.readLE a 8 = S1.mem.readLE a 8 := by
      intro a h
      rw [q2]; exact hFo.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
    have hmod : (256:Nat) ^ 8 = 2 ^ 64 := rfl
    refine hcont S2 (S'.regs 0).toNat ?_
    unfold MidInv
    refine ⟨q1, hi5, hrem, (S'.regs 0).isLt, ?a0, ?a1, ?a4, ?afl, ?asp, ?a29, ?a28, ?a18, ?mi, ?mlen, ?mrem, ?mW, ?frm, ?x30, ?x29, ?xz, ?xp, ?tab, ?val, ?env, hfb, (hclo ▸ hdig), ?hd, hall⟩
    case a0 => rw [q4]; exact bvo _
    case a1 => rw [q5]; exact hz1
    case a4 => rw [q6, hle]
    case afl => rw [q10, hle]
    case asp => rw [q3, k1, c2, rsp]
    case a29 => rw [q8, k29, c3, r29]
    case a28 => rw [q7, k28, c4, r28]
    case a18 => rw [q9, k18, c5, r18]
    case hd => rw [hdv, hclo]
    case mi =>
      rw [hrS' _ (by omega), c1]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [hmod]; exact Nat.mod_eq_of_lt (by omega)
    case mlen =>
      rw [hrS' _ (by omega), c1]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [hmod]; exact Nat.mod_eq_of_lt (by omega)
    case mrem =>
      rw [hrS' _ (by omega), c1]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
      rw [hmod]; have := nS.isLt; simp only [Nat.reducePow] at this; omega
    case mW =>
      rw [hrS' _ (by omega), c1]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [hmod, Nat.mod_eq_of_lt (Util.readLE8_lt _ _), Nat.mul_comm]; exact mtab i hi5
    case frm => rw [q2]; exact hFs'
    case x30 =>
      have := klr; rw [hsp1] at this
      rw [q2, this, hS1rd _ (by omega)]; exact m1
    case x29 =>
      have := kfp; rw [hsp1, show s.sp.toNat - 160 - 8 = s.sp.toNat - 168 by omega] at this
      rw [q2, this, hS1rd _ (by omega)]; exact m2'
    case xz => rw [hrS' _ (by omega), hS1rd _ (by omega)]; exact m3
    case xp => rw [hrS' _ (by omega), hS1rd _ (by omega)]; exact m4
    case tab =>
      intro k hk
      rw [hrS' _ (by omega), hS1rd _ (by omega)]; exact mtab k hk
    case val =>
      unfold Janus.Spec.val256
      rw [q2, ← mval]; unfold Janus.Spec.val256
      rw [hFo.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), hF1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    case env =>
      refine Env.frame0 hMod.1 hEnvS ?_ ?_ ?_ (by omega)
      · rw [q3, hr_sp]; refine ⟨by omega, by omega, by omega⟩
      · rw [q7, k28, c4, r28]
      · rw [q2]; exact hFS'
    all_goals sorry
  · -- error
    have hr_sp : S'.sp.toNat = s.sp.toNat - 160 := by rw [k1]; exact hsp1
    have hEnvS' := hEnvS
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnvS'
    have hOut : ∀ a n, s.sp.toNat - 112 ≤ a → a + n ≤ hi → lo ≤ a →
        Outside a n (R.rt ++ R2.priv ++ [(s.sp.toNat - 4440, s.sp.toNat - 112)]) := by
      intro a n h1 h2 h3
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨Outside.of_sub e9 (by omega) (by omega), Outside.of_sub e10 (by omega) (by omega)⟩, by omega⟩
    have hbyt : ∀ k, k < nS.toNat - 19 * i - clo → Fv256.C.bytesAt S1.mem (pS.toNat + clo) k =
        Fv256.C.bytesAt s.mem pS.toNat (clo + k) := by
      intro k hk; unfold Fv256.C.bytesAt
      rw [hFs1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; rw [Nat.add_assoc]
    rw [hpn, hln] at hA
    have hnot : ¬ allDec (Fv256.C.bytesAt s.mem pS.toNat) (chunkBounds nS.toNat 0 i).1 (chunkBounds nS.toNat 0 i).2 := by
      intro hh
      apply hA
      rw [chunk_allDec_iff (Fv256.C.bytesAt s.mem pS.toNat) (Fv256.C.bytesAt S1.mem (pS.toNat + clo)) clo
        (nS.toNat - 19 * i - clo) hbyt]
      have e : clo + (nS.toNat - 19 * i - clo) = (chunkBounds nS.toNat 0 i).2 := by rw [chunk_hi]; omega
      rw [e, hclo]; exact hh
    have hfd : fromDec (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat 0 = .syntax clo (nS.toNat - 19 * i - clo) := by
      refine fromDec_syntax_of_some _ _ _ _ (by omega) ?_
      rw [hfb, fb_bad _ _ _ hi5 hrem hnot, chunk_hi, hclo]
    have hacc : S'.mem.accessible (S'.sp.toNat + 48) 8 false = true := by
      rw [hfrE.accessible, hF1.accessible]
      exact Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ e5 (by omega) (by omega))
    have hr : S'.mem.readLE (S'.sp.toNat + 48) 8 = nS.toNat - 19 * i := by
      have ea : S'.sp.toNat + 48 = s.sp.toNat - 112 := by omega
      rw [ea, hfrE.readLE _ _ (hOut _ _ (by omega) (by omega) (by omega)), c1]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
      rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; have := nS.isLt; simp only [Nat.reducePow] at this; omega
    have hsp64 : S'.sp.toNat + 48 < 2 ^ 64 := by omega
    have hal : S'.sp.toNat % 16 = 0 := by rw [hr_sp]; omega
    refine Fv256.Arm64.SegCompose.seg_trans (fd_ret_to_mid impl S' s.sp.toNat (nS.toNat - 19 * i) RA hRA (by rw [hpc', c6]) hr_sp hacc hr hsp64 hal) ?_
    intro S2 hpc2 hq2
    obtain ⟨q1, q2, q3, q4, q5, qr2, q6, q7, q8, q9, q10⟩ := hq2
    have hS2sp : S2.sp.toNat = s.sp.toNat - 160 := by rw [q3]; exact hr_sp
    have hx29 : S2.mem.readLE (S2.sp.toNat - 8) 8 = (s.regs 29).toNat := by
      have := kfp; rw [hsp1, show s.sp.toNat - 160 - 8 = s.sp.toNat - 168 by omega] at this
      rw [hS2sp, show s.sp.toNat - 160 - 8 = s.sp.toNat - 168 by omega, q2, this, hS1rd _ (by omega)]; exact m2'
    have hx30 : S2.mem.readLE S2.sp.toNat 8 = (s.regs 30).toNat := by
      have := klr; rw [hsp1] at this
      rw [hS2sp, q2, this, hS1rd _ (by omega)]; exact m1
    have hacc2 : S2.mem.accessible (S2.sp.toNat - 8) 16 false = true := by
      rw [q2, hfrE.accessible, hF1.accessible]
      exact Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ e5 (by omega) (by omega))
    have hz1' : S2.regs 1 ≠ 0 := by
      rw [q5, hz3]; intro h; have := congrArg BitVec.toNat h; simp at this
    refine Fv256.Arm64.SegCompose.seg_mono (fd_err_ret impl S2 (s.regs 29) (s.regs 30) q1 hz1' hx29 hx30 hacc2
      (by omega) (by omega) (by omega) (by omega) (by omega)) ?_
    intro S'' hq''
    obtain ⟨u1, u0, u2, u29, u28, u18, umem⟩ := hq''
    have hpD' : pS.toNat + nS.toNat ≤ z.toNat ∨ z.toNat + 32 ≤ pS.toNat := hpD
    have hst0 : Outside strconvErrSyntax 16 [(lo, hi), (z.toNat, z.toNat + 32)] := by
      have a1 := e14 (strconvErrSyntax, strconvErrSyntax + 16) (by simp [staticRanges])
      have a2 := hzS (strconvErrSyntax, strconvErrSyntax + 16) (by simp [staticRanges])
      simp only [outside_cons, outside_nil, and_true, Nat.add_sub_cancel_left] at a1 a2 ⊢
      exact ⟨a1, a2⟩
    unfold FdPost
    refine ⟨?_, ?_, ?_, ?_, Or.inr (Or.inr ⟨clo, nS.toNat - 19 * i - clo, hfd, q, t, ?_, ?_, ?_, ?_⟩)⟩
    · rw [u1, q3, k1, c2, rsp]; bv_omega
    · rw [u29]
    · rw [u28, q7, k28, c4, r28]
    · rw [u18, q9, k18, c5, r18]
    · rw [u0, q5]; exact hz3
    · rw [u2, qr2]; exact hz2
    · have hpn' : (BitVec.ofNat 64 (pS.toNat + clo)).toNat = pS.toNat + clo := by rw [← hp]; exact hpn
      have hln' : (BitVec.ofNat 64 (nS.toNat - 19 * i - clo)).toNat = nS.toNat - 19 * i - clo := by rw [← hl]; exact hln
      rw [hp, hl] at hobj
      refine TeObj.congr hobj (by rw [c4, r28]) ?_ ?_ ?_ (by rw [umem, q2])
      · exact hFs1.readLE _ _ (Outside.of_sub hst0 (Nat.le_refl _) (by decide))
      · exact hFs1.readLE _ _ (Outside.of_sub hst0 (by decide) (by decide))
      · intro k hk
        rw [hpn']; rw [hln'] at hk
        refine hFs1.readLE _ _ ?_
        simp only [outside_cons, outside_nil, and_true]
        exact ⟨out_sub _ _ _ _ _ _ hpC (by omega) (by omega), out_sub _ _ _ _ _ _ hpD' (by omega) (by omega)⟩
    · have hFB1 : MemFrame s.mem S1.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)]) :=
        hFs1.mono (by
          intro a n h
          simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
          exact h.2)
      have hFB2 : MemFrame S1.mem S'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)]) :=
        hfrE.mono (by
          intro a n h
          simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
          exact ⟨h.1, win_sub _ _ _ _ _ _ h.2.1 (by omega) (by omega)⟩)
      have h3 : MemFrame S'.mem S''.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)]) := by
        rw [umem, q2]; exact MemFrame.refl _ _
      exact (hFB1.trans hFB2 (fun a n h => ⟨h, h⟩)).trans h3 (fun a n h => ⟨h, h⟩)

end Fv256.Arm64.SfdFd
