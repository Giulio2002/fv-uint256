import Fv256.Amd64.SfdFdMid

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd

namespace Fv256.Amd64.SfdFd

theorem out_sub (x k lo hi p n : Nat) (h : p + n ≤ lo ∨ hi ≤ p) (h1 : p ≤ x) (h2 : x + k ≤ p + n) :
    x + k ≤ lo ∨ hi ≤ x := by omega

theorem win_sub (a n lo hi lo' hi' : Nat) (h : a + n ≤ lo ∨ hi ≤ a) (h1 : lo ≤ lo') (h2 : hi' ≤ hi) :
    a + n ≤ lo' ∨ hi' ≤ a := by omega

theorem bvo (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- after `ParseUint` returned (either call site): the digits case reaches the merge point and continues with `hcont`;
the error case returns `(BX, CX)` -/
theorem fd_post_call (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State)
    (hpre : FdPre R R2 T b L lo hi z pS nS s)
    (S : State) (i : Nat) (hI : FdInv R R2 T b L lo hi z pS nS s i S) (hi5 : i < 5) (hrem : 19 * i < nS.toNat)
    (clo : Nat) (hclo : clo = (chunkBounds nS.toNat 0 i).1) (p len : BitVec 64)
    (hp : p = BitVec.ofNat 64 (pS.toNat + clo)) (hl : len = BitVec.ofNat 64 (nS.toNat - 19 * i - clo))
    (RA : Nat) (hRA : RA = 4933783 ∨ RA = 4933806) (S1 : State) (hS1 : PwCtx s S i nS RA S1)
    (S' : State) (hpost : PwPost R R2 T b L ((s.regs 4).toNat - 4432) ((s.regs 4).toNat - 104) p len S1 S')
    (hcont : ∀ (S2 : State) (d : Nat), MidInv R R2 T b L lo hi z pS nS s i d S2 →
      ReachesRet (Extracted.program.link impl) (retAddrOf s) S2 (FdPost R R2 T b L lo hi z pS nS s)) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S' (FdPost R R2 T b L lo hi z pS nS s) := by
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0, h3, h1, hn78, hMod, hEnv0, hlo, hhi, hMult, hEOF, hEOFo, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp'⟩, hpW, hpz, hCA, hfin⟩ := hpre
  have hI' := hI
  obtain ⟨hpc, hi5', r0, r3, r2, r1, r6, r4, r5, r14, rx15, rdf, rfs, hfr, mret, mbp, mz, mp, mtab, mval, hEnvS, hfb, hall⟩ := hI'
  obtain ⟨cmf, cra, ci, cw, cv1, cv2, c4, c5, c14, cx, cdf, cfs⟩ := hS1
  obtain ⟨⟨k1, k2, k3, k4, k5, k6, k7⟩, hcase⟩ := hpost
  have hEnvS' := hEnvS
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnvS'
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 144 := by rw [r4]; exact bv_sub_c _ 144 (by decide) (by omega)
  have hs1 : (S1.regs 4).toNat = (s.regs 4).toNat - 152 := by rw [c4]; exact bv_sub_c _ 152 (by decide) (by omega)
  have hS'4 : S'.regs 4 = s.regs 4 - 144#64 := by rw [k2, c4]; exact bv_152_8 _
  have hRAlt : RA < 2 ^ 64 := by rcases hRA with h | h <;> subst h <;> decide
  have hk1 : S'.rip = BitVec.ofNat 64 RA := by
    rw [k1]; simp only [retAddrOf]; rw [hs1, cra]
  have hbn : (nS.toNat - 19 * i - clo) ≤ 19 := by rw [hclo, chunk_lo_eq]; omega
  have hbn1 : 1 ≤ nS.toNat - 19 * i - clo := by rw [hclo, chunk_lo_eq]; omega
  have hpn : p.toNat = pS.toNat + clo := by
    rw [hp, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hclo; rw [chunk_lo_eq] at this; omega)
  have hln : len.toNat = nS.toNat - 19 * i - clo := by rw [hl, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hmfA : MemFrame S.mem S1.mem [(lo, hi), (z.toNat, z.toNat + 32)] := cmf.mono (by
    intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
  have hFs1 : MemFrame s.mem S1.mem [(lo, hi), (z.toNat, z.toNat + 32)] := hfr.trans hmfA (by
    intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
  have hbyt : ∀ k, k < nS.toNat - 19 * i - clo → Fv256.C.bytesAt S1.mem (pS.toNat + clo) k =
      Fv256.C.bytesAt s.mem pS.toNat (clo + k) := by
    intro k hk; unfold Fv256.C.bytesAt
    rw [hFs1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; rw [Nat.add_assoc]
  have hl8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  have hSr : ∀ a, (a + 8 ≤ (s.regs 4).toNat - 152 ∨ (s.regs 4).toNat - 48 ≤ a) → S1.mem.readLE a 8 = S.mem.readLE a 8 :=
    fun a ha => cmf.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
  rcases hcase with ⟨hA, hv, hz3, hz1, hE', hfrOk⟩ | ⟨hA, hz0', ⟨q, t, hz3, hz1, hobj⟩, hfrE⟩
  · -- digits
    have hfrO : MemFrame S1.mem S'.mem [((s.regs 4).toNat - 248, (s.regs 4).toNat - 112)] := hfrOk.mono (by
      intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; rw [hs1]; omega)
    have hFS' : MemFrame S.mem S'.mem [((s.regs 4).toNat - 248, (s.regs 4).toNat - 48)] := cmf.trans hfrO (by
      intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    have hFS2 : MemFrame S.mem S'.mem [(lo, hi), (z.toNat, z.toNat + 32)] := hFS'.mono (by
      intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    have hFS1 : MemFrame S.mem S'.mem [(lo, hi)] := hFS'.mono (by
      intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    have hFs' : MemFrame s.mem S'.mem [(lo, hi), (z.toNat, z.toNat + 32)] := hfr.trans hFS2 (by
      intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    rw [hpn, hln] at hA hv
    have hA' := (chunk_allDec_iff (Fv256.C.bytesAt s.mem pS.toNat) (Fv256.C.bytesAt S1.mem (pS.toNat + clo)) clo
      (nS.toNat - 19 * i - clo) hbyt).1 hA
    have hdig : allDec (Fv256.C.bytesAt s.mem pS.toNat) clo (nS.toNat - 19 * i) := by
      have e : clo + (nS.toNat - 19 * i - clo) = nS.toNat - 19 * i := by omega
      rw [e] at hA'; exact hA'
    have hdv : (S'.regs 0).toNat = decSum (Fv256.C.bytesAt s.mem pS.toNat) clo (nS.toNat - 19 * i - clo) := by
      rw [hv]; exact chunk_decSum _ _ _ _ hbyt
    have hz3' : S'.regs 3 = 0 := hz3
    refine Fv256.SegCompose.seg_trans (fd_ret_to_mid impl S' RA hRA hk1 hz3') ?_
    intro S2 hpc2 hq2
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ := hq2
    have hrdS : ∀ a, (a + 8 ≤ (s.regs 4).toNat - 248 ∨ (s.regs 4).toNat - 48 ≤ a) → S2.mem.readLE a 8 = S.mem.readLE a 8 := by
      intro a ha; rw [q2]; exact hFS'.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
    have hrdS1 : ∀ a, (a + 8 ≤ (s.regs 4).toNat - 248 ∨ (s.regs 4).toNat - 112 ≤ a) → S2.mem.readLE a 8 = S1.mem.readLE a 8 := by
      intro a ha; rw [q2]; exact hfrO.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
    refine hcont S2 (S'.regs 0).toNat ?_
    unfold MidInv
    refine ⟨q1, hi5, hrem, (S'.regs 0).isLt, ?a0, ?a3, ?a1, ?a4, ?a5, ?a14, ?ax, ?adf, ?afs, ?mi, ?mlen, ?mrem, ?mW, ?frm, ?mretM, ?mbpM,
      ?xz, ?xp, ?tab, ?val, ?env, hfb, (hclo ▸ hdig), ?hd, hall⟩
    case a0 => rw [q3]; exact bvo _
    case a3 => rw [q5, hz3']
    case a1 => rw [q4, hz1]
    case a4 => rw [q6, hS'4]
    case a5 => rw [q7, k3, c5]
    case a14 => rw [q8, k4, c14]
    case ax => rw [q9, k5, cx]
    case adf => rw [q10, k6, cdf]
    case afs => rw [q11, k7, cfs]
    case mi => rw [hrdS1 _ (by omega)]; exact ci
    case mlen => rw [hrdS1 _ (by omega)]; exact cv1
    case mrem => rw [hrdS1 _ (by omega)]; exact cv2
    case mW => rw [hrdS1 _ (by omega)]; exact cw.trans (mtab i hi5)
    case frm => rw [q2]; exact hFs'
    case mretM => rw [hrdS _ (by omega)]; exact mret
    case mbpM => rw [hrdS _ (by omega)]; exact mbp
    case xz => rw [hrdS _ (by omega)]; exact mz
    case xp => rw [hrdS _ (by omega)]; exact mp
    case tab => intro k hk; rw [hrdS _ (by omega)]; exact mtab k hk
    case hd => rw [hdv, hclo]
    case val =>
      unfold Janus.Spec.val256
      rw [q2, ← mval]; unfold Janus.Spec.val256
      exact hFS'.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
    case env =>
      refine Env.frame0 hMod.1 hEnvS ?_ (by rw [q8, k4, c14, r14]) (by rw [q2]; exact hFS1) (by omega)
      rw [q6, hS'4, bv_sub_c _ 144 (by decide) (by omega)]; refine ⟨by omega, by omega, by omega⟩
  · -- error
    have hOut : ∀ a n, (s.regs 4).toNat - 104 ≤ a → a + n ≤ hi → lo ≤ a →
        Outside a n (R.rt ++ R2.priv ++ [((s.regs 4).toNat - 4432, (s.regs 4).toNat - 104)]) := by
      intro a n h1 h2 h3
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨Outside.of_sub e9 (by omega) (by omega), Outside.of_sub e10 (by omega) (by omega)⟩, by omega⟩
    have hnot : ¬ allDec (Fv256.C.bytesAt s.mem pS.toNat) (chunkBounds nS.toNat 0 i).1 (chunkBounds nS.toNat 0 i).2 := by
      intro hh
      have hA2 := hA
      rw [hpn, hln] at hA2
      apply hA2
      rw [chunk_allDec_iff (Fv256.C.bytesAt s.mem pS.toNat) (Fv256.C.bytesAt S1.mem (pS.toNat + clo)) clo
        (nS.toNat - 19 * i - clo) hbyt]
      have e : clo + (nS.toNat - 19 * i - clo) = (chunkBounds nS.toNat 0 i).2 := by rw [chunk_hi]; omega
      rw [e, hclo]; exact hh
    have hfd : fromDec (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat 0 = .syntax clo (nS.toNat - 19 * i - clo) := by
      refine fromDec_syntax_of_some _ _ _ _ (by omega) ?_
      rw [hfb, fb_bad _ _ _ hi5 hrem hnot, chunk_hi, hclo]
    have hS'4n : (S'.regs 4).toNat = (s.regs 4).toNat - 144 := by rw [hS'4]; exact bv_sub_c _ 144 (by decide) (by omega)
    have hbp : S'.mem.readLE ((S'.regs 4).toNat + 136) 8 = (s.regs 5).toNat := by
      have ea : (S'.regs 4).toNat + 136 = (s.regs 4).toNat - 8 := by omega
      rw [ea, hfrE.readLE _ _ (hOut _ _ (by omega) (by omega) (by omega)), hSr _ (by omega)]; exact mbp
    have hret : S'.mem.readLE ((S'.regs 4).toNat + 144) 8 = (retAddrOf s).toNat := by
      have ea : (S'.regs 4).toNat + 144 = (s.regs 4).toNat := by omega
      rw [ea, hfrE.readLE _ _ (hOut _ _ (by omega) (by omega) (by omega)), hSr _ (by omega)]
      simp only [retAddrOf, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (Util.readLE8_lt _ _)]
      exact mret
    have hra47 : (retAddrOf s).toNat < 2 ^ 47 := by
      simp only [retAddrOf, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (Util.readLE8_lt _ _)]; exact hra2
    have hz3ne : S'.regs 3 ≠ 0 := by rw [hz3]; decide
    have hacc : S'.mem.accessible ((S'.regs 4).toNat + 136) 16 false = true := by
      rw [hfrE.accessible, cmf.accessible]
      exact Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ e5 (by omega) (by omega))
    have hsp64 : (S'.regs 4).toNat + 152 < 2 ^ 64 := by omega
    refine Fv256.SegCompose.seg_trans (fd_err_ret impl S' RA hRA (retAddrOf s) (s.regs 5) hra47 hk1 hz3ne hbp hret hacc hsp64) ?_
    intro S'' hpc'' hq''
    obtain ⟨u0, u3, u4, u5, u14, ux, udf, ufs, umem⟩ := hq''
    have hst0 : Outside strconvErrSyntax 16 [(lo, hi), (z.toNat, z.toNat + 32)] := by
      have a1 := e14 (strconvErrSyntax, strconvErrSyntax + 16) (by simp [staticRanges])
      have a2 := hzS (strconvErrSyntax, strconvErrSyntax + 16) (by simp [staticRanges])
      simp only [outside_cons, outside_nil, and_true, Nat.add_sub_cancel_left] at a1 a2 ⊢
      exact ⟨a1, a2⟩
    have hpD' : pS.toNat + nS.toNat ≤ z.toNat ∨ z.toNat + 32 ≤ pS.toNat := hpz.resolve_left (by omega)
    have hpW' : pS.toNat + nS.toNat ≤ lo ∨ hi ≤ pS.toNat := hpW.resolve_left (by omega)
    refine ReachesRet.done hpc'' ?_
    unfold FdPost Fv256.C.Kept
    refine ⟨⟨hpc'', ?_, u5, ?_, ?_, ?_, ?_⟩, Or.inr (Or.inr ⟨clo, nS.toNat - 19 * i - clo, hfd, q, t, ?_, ?_, ?_, ?_⟩)⟩
    · rw [u4, hS'4]; bv_omega
    · rw [u14, k4, c14]
    · rw [ux, k5, cx, hx15]
    · rw [udf, k6, cdf, hdf]
    · rw [ufs, k7, cfs]
    · rw [u0, hz3]
    · rw [u3, hz1]
    · have hpn' : (BitVec.ofNat 64 (pS.toNat + clo)).toNat = pS.toNat + clo := by rw [← hp]; exact hpn
      have hln' : (BitVec.ofNat 64 (nS.toNat - 19 * i - clo)).toNat = nS.toNat - 19 * i - clo := by rw [← hl]; exact hln
      rw [hp, hl] at hobj
      refine TeObj.congr_mem (TeObj.congr_src hobj (by rw [c14]) ?_ ?_ ?_) (by rw [umem])
      · exact hFs1.readLE _ _ (Outside.of_sub hst0 (Nat.le_refl _) (by decide))
      · exact hFs1.readLE _ _ (Outside.of_sub hst0 (by decide) (by decide))
      · intro k hk
        rw [hpn']; rw [hln'] at hk
        refine hFs1.readLE _ _ ?_
        simp only [outside_cons, outside_nil, and_true]
        exact ⟨out_sub _ _ _ _ _ _ hpW' (by omega) (by omega), out_sub _ _ _ _ _ _ hpD' (by omega) (by omega)⟩
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
        rw [umem]; exact MemFrame.refl _ _
      exact (hFB1.trans hFB2 (fun a n h => ⟨h, h⟩)).trans h3 (fun a n h => ⟨h, h⟩)

end Fv256.Amd64.SfdFd
