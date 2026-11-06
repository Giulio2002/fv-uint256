import Fv256.Arm64.SfdFdC
import Fv256.Arm64.SfdFdMid

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdEnv Fv256.Arm64.SfdToError Fv256.Arm64.SfdPw Fv256.Arm64.SfdFd

namespace Fv256.Arm64.SfdFd

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
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ := hq2
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
  · sorry

end Fv256.Arm64.SfdFd
