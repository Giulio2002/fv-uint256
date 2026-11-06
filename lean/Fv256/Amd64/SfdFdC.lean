import Fv256.Amd64.SfdFdB

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd

namespace Fv256.Amd64.SfdFd

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- round `i > 0`: `tmp = d`, `tmp = tmp * 10^(19 i)` (`Mul`), `z += tmp` -/
theorem fd_midK (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State)
    (hn78 : nS.toNat ≤ 78) (hlo : lo + 4432 ≤ (s.regs 4).toNat) (hhi : (s.regs 4).toNat + 32 ≤ hi)
    (hal : (s.regs 4).toNat % 8 = 0) (hs64 : (s.regs 4).toNat + 32 < 2 ^ 64)
    (hzw : s.mem.accessible z.toNat 32 true = true) (hzb : z.toNat + 32 ≤ 2 ^ 48)
    (hzlh : z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat) (hzR : Outside z.toNat 32 R.rt ∨ InRanges z.toNat 32 L)
    (hzP : Outside z.toNat 32 R2.priv) (hzS : ∀ r ∈ staticRanges T, Outside r.1 (r.2 - r.1) [(z.toNat, z.toNat + 32)])
    (hzg : (s.regs 14).toNat + 16 + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 14).toNat + 16)
    (hMod : Mod R R2 T L) (hMult : MultOK z.toNat lo hi s.mem)
    (hfin : allDec (Fv256.C.bytesAt s.mem pS.toNat) 0 nS.toNat → decSum (Fv256.C.bytesAt s.mem pS.toNat) 0 nS.toNat < 2 ^ 256)
    (S : State) (i d : Nat) (hM : MidInv R R2 T b L lo hi z pS nS s i d S) (hi0 : i ≠ 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 m2) S (M2Inv R R2 T b L lo hi z pS nS s i) := by
  have hM' := hM
  obtain ⟨hpc, hi5, hrem, hd64, r0, r3, r1, r4, r5, r14, rx15, rdf, rfs, mi, mlen, mrem, mW, hfr, mret, mbp, mz, mp, mtab, mval, hEnv, hfb, hdig, hd, hall⟩ := hM'
  refine Fv256.SegCompose.seg_trans (fd_to_mul impl R R2 T b L lo hi z pS nS s hn78 hlo hhi S i d hM hi0) ?_
  intro S3 hpc3 hq3
  obtain ⟨q0, q3, q1, q4, q5, q14, qx, qdf, qfs, qmem⟩ := hq3
  have hmult := hMult
  obtain ⟨hMa, hMo, hMk⟩ := hmult
  obtain ⟨hWa, hWb, hWv, hWo⟩ := hMk i (by omega) (by omega)
  have hWeq : s.mem.readLE (mulTab + 8 * i) 8 = s.mem.readLE (mulTab + 8 * i) 8 := rfl
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hWo' := hWo
  simp only [outside_cons, outside_nil, and_true] at hWo'
  obtain ⟨hWo1, hWo2⟩ := hWo'
  have hbase : (s.regs 4 - 88#64).toNat = (s.regs 4).toNat - 88 := bv_sub_c _ 88 (by decide) (by omega)
  have hrs : (S3.regs 4).toNat = (s.regs 4).toNat - 152 := by rw [q4]; exact bv_sub_c _ 152 (by decide) (by omega)
  have hWn : (BitVec.ofNat 64 (s.mem.readLE (mulTab + 8 * i) 8)).toNat = s.mem.readLE (mulTab + 8 * i) 8 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hS3F : MemFrame S.mem S3.mem [((s.regs 4).toNat - 168, (s.regs 4).toNat - 144), ((s.regs 4).toNat - 88, (s.regs 4).toNat - 56)] := by
    rw [qmem]
    exact ((((MemFrame.refl S.mem _).writeLE _ (r := ((s.regs 4).toNat - 88, (s.regs 4).toNat - 56)) (by simp)
      (by dsimp only; omega) (by dsimp only; omega)).writeLE _ (r := ((s.regs 4).toNat - 88, (s.regs 4).toNat - 56)) (by simp)
      (by dsimp only; omega) (by dsimp only; omega)).writeLE _ (r := ((s.regs 4).toNat - 88, (s.regs 4).toNat - 56)) (by simp)
      (by dsimp only; omega) (by dsimp only; omega)).writeLE _ (r := ((s.regs 4).toNat - 168, (s.regs 4).toNat - 144)) (by simp)
      (by dsimp only; omega) (by dsimp only; omega)
  have hS3F' : MemFrame S.mem S3.mem [(lo, hi), (z.toNat, z.toNat + 32)] := hS3F.mono (by
    intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
  have hF3 : MemFrame s.mem S3.mem [(lo, hi), (z.toNat, z.toNat + 32)] := hfr.trans hS3F' (by
    intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
  have hS3acc : ∀ a n w, S3.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hF3.accessible a n w
  have hS3r : S3.mem.readLE ((s.regs 4).toNat - 152) 8 = 4933898 := by
    rw [qmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
    all_goals (try (rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (by decide)))
  have haccs : ∀ a n, lo ≤ a → a + n ≤ hi → s.mem.accessible a n true = true := by
    intro a n h1 h2
    rw [← hfr.accessible]
    exact Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  have haccS3 : ∀ a n, lo ≤ a → a + n ≤ hi → S3.mem.accessible a n true = true := by
    intro a n h1 h2
    rw [hS3acc, ← hfr.accessible]
    exact Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  refine ReachesRet.call (Fv256.B.summary_link impl (Fv256.Amd64.SfdMul.mul_sum (s.regs 4 - 88#64) (s.regs 4 - 88#64)
    (BitVec.ofNat 64 (s.mem.readLE (mulTab + 8 * i) 8)))) hpc3 ?pre ?cont
  case pre =>
    refine ⟨⟨?_, ?_, ?_, ?_⟩, q0, q3, q1, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals try simp only [regSP, hrs, hbase, hS3acc, hS3r, Nat.reduceMul]
    all_goals first
      | omega
      | decide
      | (rw [qx]; exact rx15)
      | (rw [qdf]; exact rdf)
      | (exact haccs _ _ (by omega) (by omega))
      | (exact Arm64.Memory.accessible_weaken _ (haccs _ _ (by omega) (by omega)))
      | (exact haccS3 _ _ (by omega) (by omega))
      | (exact Arm64.Memory.accessible_weaken _ (haccS3 _ _ (by omega) (by omega)))
      | (simp only [BitVec.toNat_ofNat, hWn]; first | omega | exact hWa)
      | (rw [hWn, hS3acc]; exact hWa)
  case cont =>
    intro S'' hpc'' hpost
    obtain ⟨⟨k1, k2, k3, k4, k5, k6, k7⟩, p0, pval, pfr⟩ := hpost
    simp only [regSP] at pfr
    have hpfr : MemFrame S3.mem S''.mem [((s.regs 4).toNat - 168, (s.regs 4).toNat - 144), ((s.regs 4).toNat - 88, (s.regs 4).toNat - 56)] :=
      pfr.mono (by
        intro a n h; simp only [outside_cons, outside_nil, and_true, hrs, hbase] at h ⊢; omega)
    have hFo : MemFrame S.mem S''.mem [((s.regs 4).toNat - 168, (s.regs 4).toNat - 144), ((s.regs 4).toNat - 88, (s.regs 4).toNat - 56)] :=
      hS3F.trans hpfr (by
        intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    have hFo' : MemFrame S.mem S''.mem [(lo, hi), (z.toNat, z.toNat + 32)] := hFo.mono (by
      intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    have hFs'' : MemFrame s.mem S''.mem [(lo, hi), (z.toNat, z.toNat + 32)] := hfr.trans hFo' (by
      intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    have hrd : ∀ a, Outside a 8 [((s.regs 4).toNat - 168, (s.regs 4).toNat - 144), ((s.regs 4).toNat - 88, (s.regs 4).toNat - 56)] →
        S''.mem.readLE a 8 = S.mem.readLE a 8 := fun a h => hFo.readLE a 8 h
    have hpc4 : S''.rip = BitVec.ofNat 64 4933898 := by
      rw [k1]; simp only [retAddrOf]; rw [hrs, hS3r]
    have hr4' : S''.regs 4 = s.regs 4 - 144#64 := by rw [k2, q4]; exact bv_152_8 _
    have hS''acc : ∀ a n w, S''.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hFs''.accessible a n w
    have hadd := fd_add impl s S'' z nS i lo hi hlo hhi hzb hzlh hn78 hrem hpc4 hr4' p0
      (by rw [hrd _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact mz)
      (by rw [hrd _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact mrem)
      (by rw [hrd _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact mi)
      hal hs64 (by rw [hS''acc]; exact haccs _ _ (by omega) (by omega)) (by rw [hS''acc]; exact hzw)
    refine Fv256.SegCompose.seg_mono hadd ?_
    intro S4 hq4
    obtain ⟨g1, g6, g2, g8, gfl, g4, g5, g14, gx, gdf, gfs, gfr, gval⟩ := hq4
    have hle : nS - BitVec.ofNat 64 (19 * i) = BitVec.ofNat 64 (nS.toNat - 19 * i) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := nS.isLt; simp only [Nat.reducePow] at *; omega
    have hrd4 : ∀ a, Outside a 8 [((s.regs 4).toNat - 168, (s.regs 4).toNat - 144), ((s.regs 4).toNat - 88, (s.regs 4).toNat - 56)] →
        (a + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ a) → S4.mem.readLE a 8 = S.mem.readLE a 8 := by
      intro a h1 h2
      rw [gfr.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)]
      exact hrd a h1
    have hgfr' : MemFrame S''.mem S4.mem [(lo, hi), (z.toNat, z.toNat + 32)] :=
      gfr.mono (by intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    have hFS4 : MemFrame S.mem S4.mem [(lo, hi), (z.toNat, z.toNat + 32)] :=
      hFo'.trans hgfr' (by
        intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    have hFs4 : MemFrame s.mem S4.mem [(lo, hi), (z.toNat, z.toNat + 32)] :=
      hfr.trans hFS4 (by intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    have hg14 : S4.regs 14 = S.regs 14 := by rw [g14, k4, q14]
    unfold M2Inv
    refine ⟨g1, hi5, hrem, g6, g2, ?r8, ?fl, ?r4, ?r5, ?r14, ?xm, ?dff, ?fsb, ?mlen, hFs4, ?mretM, ?mbpM, ?xz, ?xp, ?tab, ?val, ?env, ?fb, ?hall⟩
    case r8 => rw [g8, hle]
    case fl => rw [gfl, hle]
    case r4 => rw [g4, hr4']
    case r5 => rw [g5, k3, q5, r5]
    case r14 => rw [g14, k4, q14, r14]
    case xm => rw [gx, k5, qx, rx15]
    case dff => rw [gdf, k6, qdf, rdf]
    case fsb => rw [gfs, k7, qfs, rfs]
    case mlen => rw [hrd4 _ (by simp only [outside_cons, outside_nil, and_true]; omega) (by omega)]; exact mlen
    case mretM => rw [hrd4 _ (by simp only [outside_cons, outside_nil, and_true]; omega) (by omega)]; exact mret
    case mbpM => rw [hrd4 _ (by simp only [outside_cons, outside_nil, and_true]; omega) (by omega)]; exact mbp
    case xz => rw [hrd4 _ (by simp only [outside_cons, outside_nil, and_true]; omega) (by omega)]; exact mz
    case xp => rw [hrd4 _ (by simp only [outside_cons, outside_nil, and_true]; omega) (by omega)]; exact mp
    case tab =>
      intro k hk
      rw [hrd4 _ (by simp only [outside_cons, outside_nil, and_true]; omega) (by omega)]; exact mtab k hk
    case env =>
      refine Env.frame hMod.1 hEnv ?_ hg14 hFS4 hzR hzP hzS (by rw [r14]; exact hzg)
      rw [g4, hr4', bv_sub_c _ 144 (by decide) (by omega)]; refine ⟨by omega, by omega, by omega⟩
    case fb => rw [hfb]; exact fb_good _ _ _ hi5 hrem (by rw [chunk_hi]; exact hdig)
    case hall => have := hdig; rw [chunk_lo_eq] at this; exact allDec_join this hall
    case val =>
      have hdlt : (S.regs 0).toNat < 2 ^ 64 := (S.regs 0).isLt
      have hv1 : Janus.Spec.val256 S''.mem z.toNat = accV (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat i := by
        rw [← mval]; unfold Janus.Spec.val256
        exact hFo.readLE z.toNat 32 (by simp only [outside_cons, outside_nil, and_true]; omega)
      have hA3 : valueAt S3 (s.regs 4 - 88#64) 32 = d := by
        unfold valueAt
        rw [hbase, qmem]
        exact z_store3 _ _ _ _ _ _ (by omega) hd64 (by omega)
      have hB3 : valueAt S3 (BitVec.ofNat 64 (s.mem.readLE (mulTab + 8 * i) 8)) 32 = 10 ^ (19 * i) := by
        unfold valueAt
        rw [hWn, ← hWv]; unfold Janus.Spec.val256
        exact hF3.readLE _ _ hWo
      have hv5 : Janus.Spec.val256 S''.mem ((s.regs 4).toNat - 88) = (d * 10 ^ (19 * i)) % 2 ^ 256 := by
        have := pval
        rw [hA3, hB3] at this
        unfold valueAt Fv256.Spec.mul at this
        rw [hbase] at this
        simpa [Fv256.Spec.W, Janus.Spec.val256] using this
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

end Fv256.Amd64.SfdFd
