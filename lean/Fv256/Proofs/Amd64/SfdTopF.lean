import Fv256.Proofs.Amd64.SfdTopE

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd
  Fv256.Amd64.SfdTopSpec Fv256.Amd64.SfdTopCfg Fv256.Amd64.SfdTopBr

namespace Fv256.Amd64.SfdTop

open Fv256.TopMath

theorem bv_72_8 (a : BitVec 64) : a - 72#64 + 8#64 = a - 64#64 := by bv_omega
theorem bv_64_72 (a : BitVec 64) : a - 64#64 + 72#64 = a + 8#64 := by bv_omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- the epilogue after `fromDecimal` returns: `ADDQ $0x38,SP; POPQ BP; RET` -/
theorem top_epi (impl : List Janus.Amd64.Segment) (S1 : State) (RA : Nat) (hRA : RA = 4933361 ∨ RA = 4933330)
    (ra bp : BitVec 64) (hra : ra.toNat < 2 ^ 47) (hpc : S1.rip = BitVec.ofNat 64 RA)
    (hbp : S1.mem.readLE ((S1.regs 4).toNat + 56) 8 = bp.toNat) (hret : S1.mem.readLE ((S1.regs 4).toNat + 64) 8 = ra.toNat)
    (hacc : S1.mem.accessible ((S1.regs 4).toNat + 56) 16 false = true) (hsp64 : (S1.regs 4).toNat + 72 < 2 ^ 64) :
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) ra S1
      (fun S2 => S2.regs 0 = S1.regs 0 ∧ S2.regs 3 = S1.regs 3 ∧ S2.regs 4 = S1.regs 4 + 72#64 ∧ S2.regs 5 = bp ∧
        S2.regs 14 = S1.regs 14 ∧ S2.xmm 15 = S1.xmm 15 ∧ S2.df = S1.df ∧ S2.fsBase = S1.fsBase ∧ S2.mem = S1.mem) := by
  rcases hRA with rfl | rfl
  all_goals
    janus64_run [hbp, hret, hacc, hsp64, hra]

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- after `fromDecimal` returns: the epilogue and the documented result -/
theorem top_fin (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (Sc S1 : State) (RA : Nat) (hRA : RA = 4933361 ∨ RA = 4933330)
    (hctx : FdCtx R R2 T b L lo hi z pS nS s RA Sc) (hpc : S1.rip = BitVec.ofNat 64 RA)
    (hpost : FdPost R R2 T b L lo ((s.regs 4).toNat - 40) z (Sc.regs 3) (Sc.regs 1) Sc S1)
    (hdp : decParse (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat =
      fromDec (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)) :
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (retAddrOf s) S1 (TopPost extCfg R R2 T b L lo hi z pS nS s) := by
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0', h3', h1', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hEnv0 := env_to hEnv
  have hEnvs := hEnv0
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnvs
  obtain ⟨⟨c4, c5, c14, cx, cdf, cfs, cmf, cbp, cz, cp, cret, cenv⟩, r0, ⟨k, hk1, hk2, r3⟩, r1, hslot⟩ := hctx
  obtain ⟨⟨k1, k2, k3, k4, k5, k6, k7⟩, hcase⟩ := hpost
  have hnS := nS.isLt
  have hS1_4 : S1.regs 4 = s.regs 4 - 64#64 := by rw [k2, c4]; exact bv_72_8 _
  have hS1n : (S1.regs 4).toNat = (s.regs 4).toNat - 64 := by rw [hS1_4]; exact bv_sub_c _ 64 (by decide) (by omega)
  have hsc4 : (Sc.regs 4).toNat = (s.regs 4).toNat - 72 := by rw [c4]; exact bv_sub_c _ 72 (by decide) (by omega)
  have hpe := Fv256.TopMath.startPos_spec' (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hr1n : (Sc.regs 1).toNat = nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
    rw [r1, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  -- the bytes the callee parsed are the original bytes from `startPos`
  have hbytes : ∀ j, j < (Sc.regs 1).toNat →
      Fv256.C.bytesAt Sc.mem (Sc.regs 3).toNat j = Fv256.C.bytesAt s.mem pS.toNat (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) := by
    intro j hj
    rw [hr1n] at hj
    have hk : k = startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := hk2 (by omega)
    have h3n : (Sc.regs 3).toNat = pS.toNat + k := by
      rw [r3]; exact add_toNat _ _ (by simp only [Nat.reducePow]; omega)
    rw [h3n]
    show Sc.mem.readLE (pS.toNat + k + j) 1 = s.mem.readLE (pS.toNat + (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1
    rw [hk, Nat.add_assoc]
    exact cmf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; have := hpW.resolve_left (by omega); omega)
  have hdec : ∀ r, fromDec (Fv256.C.bytesAt Sc.mem (Sc.regs 3).toNat) (Sc.regs 1).toNat 0 = r →
      decParse (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = shiftRes (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) r := by
    intro r hr
    rw [← hr]
    exact dec_of_fd _ _ _ _ _ hpe hr1n hbytes hdp
  have hra47 : (retAddrOf s).toNat < 2 ^ 47 := by
    simp only [retAddrOf, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (Util.readLE8_lt _ _)]; exact hra2
  have hraN : (retAddrOf s).toNat = s.mem.readLE (s.regs 4).toNat 8 := by
    simp only [retAddrOf, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Util.readLE8_lt _ _)
  have hsp64 : (S1.regs 4).toNat + 72 < 2 ^ 64 := by rw [hS1n]; omega
  have fin : (∀ a n, (s.regs 4).toNat - 40 ≤ a → a + n ≤ hi → S1.mem.readLE a n = Sc.mem.readLE a n) →
      (∀ a n w, S1.mem.accessible a n w = Sc.mem.accessible a n w) →
      ∀ post : State → Prop, (∀ S2 : State, S2.rip = retAddrOf s →
        (S2.regs 0 = S1.regs 0 ∧ S2.regs 3 = S1.regs 3 ∧ S2.regs 4 = S1.regs 4 + 72#64 ∧ S2.regs 5 = (s.regs 5) ∧
          S2.regs 14 = S1.regs 14 ∧ S2.xmm 15 = S1.xmm 15 ∧ S2.df = S1.df ∧ S2.fsBase = S1.fsBase ∧ S2.mem = S1.mem) → post S2) →
      ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (retAddrOf s) S1 post := by
    intro hrd hacc post hp
    refine Fv256.SegCompose.seg_trans (top_epi impl S1 RA hRA (retAddrOf s) (s.regs 5) hra47 hpc ?_ ?_ ?_ hsp64) ?_
    · have e : (S1.regs 4).toNat + 56 = (s.regs 4).toNat - 8 := by omega
      rw [e, hrd _ _ (by omega) (by omega), cbp]
    · have e : (S1.regs 4).toNat + 64 = (s.regs 4).toNat := by omega
      rw [e, hrd _ _ (by omega) (by omega), cret, hraN]
    · rw [hacc, cmf.accessible]
      exact Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ e5 (by omega) (by omega))
    · intro S2 hpc2 hq
      exact ReachesRet.done hpc2 (hp S2 hpc2 hq)
  have hEnvOf : ∀ (S2 : State), S2.regs 4 = s.regs 4 + 8#64 → S2.regs 14 = s.regs 14 → S2.mem = S1.mem →
      MemFrame Sc.mem S1.mem [(lo, (s.regs 4).toNat - 40), (z.toNat, z.toNat + 32)] →
      Fv256.Amd64.SfdEnv.Env R R2 T b L lo hi S2 := by
    intro S2 h4 h14 hm hf
    have hs : (S2.regs 4).toNat = (s.regs 4).toNat + 8 := by
      rw [h4]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [Nat.reducePow]; omega
    exact Env.frame hMod.1 cenv ⟨by rw [hs]; omega, by rw [hs]; omega, by rw [hs]; omega⟩ (by rw [h14, c14])
      (by rw [hm]; exact hf.mono (fun a n h => outside_hi h (by omega))) hzR hzP hzS (by rw [c14]; exact hzg)
  have kept : ∀ S2 : State, S2.rip = retAddrOf s →
      (S2.regs 0 = S1.regs 0 ∧ S2.regs 3 = S1.regs 3 ∧ S2.regs 4 = S1.regs 4 + 72#64 ∧ S2.regs 5 = (s.regs 5) ∧
        S2.regs 14 = S1.regs 14 ∧ S2.xmm 15 = S1.xmm 15 ∧ S2.df = S1.df ∧ S2.fsBase = S1.fsBase ∧ S2.mem = S1.mem) →
      Fv256.C.Kept s S2 := by
    intro S2 hpc2 ⟨q0, q3, q4, q5, q14, qx, qdf, qfs, qmem⟩
    refine ⟨hpc2, ?_, q5, ?_, ?_, ?_, ?_⟩
    · rw [q4, hS1_4]; exact bv_64_72 _
    · rw [q14, k4, c14]
    · rw [qx, k5, cx, hx15]
    · rw [qdf, k6, cdf, hdf]
    · rw [qfs, k7, cfs]
  have hs2 : ∀ S2 : State, S2.regs 4 = S1.regs 4 + 72#64 → S2.regs 4 = s.regs 4 + 8#64 := by
    intro S2 h; rw [h, hS1_4]; exact bv_64_72 _
  have cmf' : MemFrame s.mem Sc.mem [(lo, hi), (z.toNat, z.toNat + 32)] := cmf.mono (by
    intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
  have hOutS : ∀ a n, (s.regs 4).toNat - 40 ≤ a → a + n ≤ hi → Outside a n [(lo, (s.regs 4).toNat - 40), (z.toNat, z.toNat + 32)] := by
    intro a n h1 h2
    simp only [outside_cons, outside_nil, and_true]
    omega
  have hOutF : ∀ a n, (s.regs 4).toNat - 40 ≤ a → a + n ≤ hi →
      Outside a n (R.rt ++ R2.priv ++ [(lo, (s.regs 4).toNat - 40), (z.toNat, z.toNat + 32)]) := by
    intro a n h1 h2
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨Outside.of_sub e9 (by omega) (by omega), Outside.of_sub e10 (by omega) (by omega)⟩, by omega, by omega⟩
  rcases hcase with ⟨hfd, a0, a3, hval, hE, hfr⟩ | ⟨v, hfd, a0, a3, hval, hE, hfr⟩ | ⟨lo1, len1, hfd, q, tt, a0, a3, hobj, hfr⟩
  · -- eof
    have hfr' : MemFrame Sc.mem S1.mem [(lo, hi), (z.toNat, z.toNat + 32)] := hfr.mono (fun a n h => outside_hi h (by omega))
    have hfr2 : MemFrame s.mem S1.mem [(lo, hi), (z.toNat, z.toNat + 32)] := cmf'.trans hfr' (fun a n h => ⟨h, h⟩)
    refine fin (fun a n h1 h2 => hfr.readLE a n (hOutS a n h1 h2)) (fun a n w => hfr.accessible a n w) _ ?_
    intro S2 hpc2 hq
    obtain ⟨q0, q3, q4, q5, q14, qx, qdf, qfs, qmem⟩ := hq
    have hE2 : Fv256.Amd64.SfdEnv.Env R R2 T b L lo hi S2 := hEnvOf S2 (hs2 S2 q4) (by rw [q14, k4, c14]) qmem hfr
    refine ⟨kept S2 hpc2 ⟨q0, q3, q4, q5, q14, qx, qdf, qfs, qmem⟩, Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, env_of hE2, ?_⟩)⟩
    · rw [hdec _ hfd]; simp [shiftRes]
    · have ho : Outside Fv256.Amd64.SfdFd.ioEOF 16 [(lo, hi), (z.toNat, z.toNat + 32)] := hEOFo
      simp only [outside_cons, outside_nil, and_true] at ho
      rw [q0, a0]
      exact (cmf.readLE Fv256.Amd64.SfdFd.ioEOF 8 (by simp only [outside_cons, outside_nil, and_true]; omega))
    · have ho : Outside Fv256.Amd64.SfdFd.ioEOF 16 [(lo, hi), (z.toNat, z.toNat + 32)] := hEOFo
      simp only [outside_cons, outside_nil, and_true] at ho
      rw [q3, a3]
      exact (cmf.readLE (Fv256.Amd64.SfdFd.ioEOF + 8) 8 (by simp only [outside_cons, outside_nil, and_true]; omega))
    · rw [qmem]; exact hval
    · rw [qmem]; exact hfr2
  · -- ok
    have hfr' : MemFrame Sc.mem S1.mem [(lo, hi), (z.toNat, z.toNat + 32)] := hfr.mono (fun a n h => outside_hi h (by omega))
    have hfr2 : MemFrame s.mem S1.mem [(lo, hi), (z.toNat, z.toNat + 32)] := cmf'.trans hfr' (fun a n h => ⟨h, h⟩)
    refine fin (fun a n h1 h2 => hfr.readLE a n (hOutS a n h1 h2)) (fun a n w => hfr.accessible a n w) _ ?_
    intro S2 hpc2 hq
    obtain ⟨q0, q3, q4, q5, q14, qx, qdf, qfs, qmem⟩ := hq
    have hE2 : Fv256.Amd64.SfdEnv.Env R R2 T b L lo hi S2 := hEnvOf S2 (hs2 S2 q4) (by rw [q14, k4, c14]) qmem hfr
    refine ⟨kept S2 hpc2 ⟨q0, q3, q4, q5, q14, qx, qdf, qfs, qmem⟩, Or.inl ⟨v, ?_, ?_, ?_, ?_, env_of hE2, ?_⟩⟩
    · rw [hdec _ hfd]; simp [shiftRes]
    · rw [q0, a0]
    · rw [q3, a3]
    · rw [qmem]; exact hval
    · rw [qmem]; exact hfr2
  · -- syntax
    have hdp2 := hdec _ hfd
    have hsyn : decParse (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = Res.syntax (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + lo1) len1 := by
      rw [hdp2]; rfl
    obtain ⟨hl1, hl2, hl3⟩ := Fv256.I.Fv256.I.decParse_syntax _ _ _ _ hsyn
    refine fin (fun a n h1 h2 => hfr.readLE a n (hOutF a n h1 h2)) (fun a n w => hfr.accessible a n w) _ ?_
    intro S2 hpc2 hq
    obtain ⟨q0, q3, q4, q5, q14, qx, qdf, qfs, qmem⟩ := hq
    have hk : k = startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := hk2 (by omega)
    have h3n : (Sc.regs 3).toNat = pS.toNat + k := by
      rw [r3]; exact add_toNat _ _ (by simp only [Nat.reducePow]; omega)
    have hst0 : Outside Fv256.Amd64.SfdEnv.strconvErrSyntax 16 [(lo, hi)] := by
      have := e14 (Fv256.Amd64.SfdEnv.strconvErrSyntax, Fv256.Amd64.SfdEnv.strconvErrSyntax + 16) (by simp [Fv256.Amd64.SfdEnv.staticRanges])
      simpa using this
    refine ⟨kept S2 hpc2 ⟨q0, q3, q4, q5, q14, qx, qdf, qfs, qmem⟩, Or.inr (Or.inr (Or.inr ⟨startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + lo1, len1, hsyn, q, tt, ?_, ?_, ?_, ?_⟩))⟩
    · exact q0.trans a0
    · rw [q3, a3]
    · have e : (Sc.regs 3).toNat + lo1 = pS.toNat + (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + lo1) := by omega
      rw [e] at hobj
      have hlen1 : (BitVec.ofNat 64 len1).toNat = len1 := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hsp1 : (BitVec.ofNat 64 (pS.toNat + (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + lo1))).toNat =
          pS.toNat + (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + lo1) := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hobj2 := TeObj.congr_src hobj (by rw [c14]) (cmf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; have := hst0; simp only [outside_cons, outside_nil, and_true] at this; omega))
        (cmf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; have := hst0; simp only [outside_cons, outside_nil, and_true] at this; omega))
        (by
          intro k' hk'
          rw [hlen1] at hk'
          rw [hsp1]
          exact cmf.readLE _ _ (by
            simp only [outside_cons, outside_nil, and_true]
            have := hpW.resolve_left (by omega)
            omega))
      exact teobj_of (TeObj.congr_mem hobj2 (by rw [qmem]))
    · have hFB1 : MemFrame s.mem Sc.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)]) :=
        cmf'.mono (by
          intro a n h
          simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
          exact h.2)
      have hFB2 : MemFrame Sc.mem S1.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)]) :=
        hfr.mono (by
          intro a n h
          simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
          exact ⟨h.1, by omega⟩)
      rw [qmem]; exact hFB1.trans hFB2 (fun a n h => ⟨h, h⟩)

end Fv256.Amd64.SfdTop
