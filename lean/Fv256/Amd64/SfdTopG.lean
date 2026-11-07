import Fv256.Amd64.SfdTopF

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd
  Fv256.Amd64.SfdTopSpec Fv256.Amd64.SfdTopCfg Fv256.Amd64.SfdTopBr

namespace Fv256.Amd64.SfdTop

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- `ErrBig256Range`: load the two words of the package variable, pop the frame, return -/
theorem top_range (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (S : State) (pcE : Nat) (hE : pcE = sfd + 0xb8 ∨ pcE = sfd + 0x8a) (hpc : S.rip = BitVec.ofNat 64 pcE)
    (hSt : TopSt R R2 T b L lo hi z pS s S)
    (hdp : decParse (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = Res.range) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S (TopPost extCfg R R2 T b L lo hi z pS nS s) := by
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0', h3', h1', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hEnv0 := env_to hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv0
  have hSt' := hSt
  obtain ⟨t4, t5, t14, tx, tdf, tfs, tmf, tbp, tz, tp, tret, tenv⟩ := hSt'
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 64 := by rw [t4]; exact bv_sub_c _ 64 (by decide) (by omega)
  have hacc : S.mem.accessible ((S.regs 4).toNat) 72 false = true := by
    rw [tmf.accessible]; exact Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ e5 (by omega) (by omega))
  have hbp : S.mem.readLE ((S.regs 4).toNat + 56) 8 = (s.regs 5).toNat := by
    have e : (S.regs 4).toNat + 56 = (s.regs 4).toNat - 8 := by omega
    rw [e]; exact tbp
  have hret : S.mem.readLE ((S.regs 4).toNat + 64) 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    have e : (S.regs 4).toNat + 64 = (s.regs 4).toNat := by omega
    rw [e]; exact tret
  have hEr : Outside Fv256.Amd64.SfdFd.ioEOF 16 [(lo, hi), (z.toNat, z.toNat + 32)] := hEOFo
  have hErA : S.mem.accessible 5995424 16 false = true := by
    rw [tmf.accessible]; exact hErr
  have hEro : 5995424 + 16 ≤ lo ∨ hi ≤ 5995424 := by
    have h := hErro; simp only [outside_cons, outside_nil, and_true] at h; exact h.1
  have hmem0 : S.mem.readLE 5995424 8 = s.mem.readLE 5995424 8 := tmf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hmem1 : S.mem.readLE (5995424 + 8) 8 = s.mem.readLE (5995424 + 8) 8 := tmf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  rcases hE with rfl | rfl
  all_goals
    janus64_run [hpc, hacc, hbp, hret, hS4, hErA, hmem0, hmem1, hEro]
    all_goals (
      refine name_state (P := TopPost extCfg R R2 T b L lo hi z pS nS s) ?_
      intro S2 hS2
      have hs2n : (S2.regs 4).toNat = (s.regs 4).toNat + 8 := by
        have h4 : S2.regs 4 = s.regs 4 + 8#64 := by simp [hS2, setRegF_apply]
        rw [h4]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [Nat.reducePow]; omega
      have hm2 : S2.mem = S.mem := by rw [hS2]
      have h14 : S2.regs 14 = s.regs 14 := by rw [hS2]; simp [setRegF_apply, t14]
      refine ⟨⟨by rw [hS2]; rfl, by simp [hS2, setRegF_apply], by simp [hS2, setRegF_apply], h14,
        by simp [hS2, tx, hx15], by first | (rw [hS2]; exact hdf.symm) | (rw [hS2]; exact tdf.trans hdf) | simp [hS2, tdf, hdf], by simp [hS2, tfs]⟩,
        Or.inr (Or.inr (Or.inl ⟨hdp, ?_, ?_, ?_, ?_, ?_⟩))⟩
      · rw [hS2]; simp [setRegF_apply]; rfl
      · rw [hS2]; simp [setRegF_apply]; rfl
      · rw [hm2]; unfold Janus.Spec.val256
        exact tmf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
      · refine env_of (Env.frame0 hMod.1 tenv ⟨by rw [hs2n]; omega, by rw [hs2n]; omega, by rw [hs2n]; omega⟩ (by rw [h14, t14]) ?_ (by omega))
        rw [hm2]; exact MemFrame.refl _ _
      · rw [hm2]; exact tmf.mono (by intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega))

end Fv256.Amd64.SfdTop
