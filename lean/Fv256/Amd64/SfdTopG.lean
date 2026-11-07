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
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (retAddrOf s) S (TopPost extCfg R R2 T b L lo hi z pS nS s) := by
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

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- more than 78 digits: jump to the error exit -/
theorem top_c2 (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 (sfd + 0x57)) (hM : TopMid R R2 T b L lo hi z pS nS s S)
    (hgt : 78 < nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) :
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (BitVec.ofNat 64 (sfd + 0xb8)) S (TopSt R R2 T b L lo hi z pS s) := by
  obtain ⟨hSt, h0, ⟨k, hk1, hk2, h3⟩, h1⟩ := hM
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0', h3', h1', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hnS := nS.isLt
  have hsp := Fv256.TopMath.startPos_spec' (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hmI := ofNat_toInt (nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (by omega)
  janus64_run [hpc, h1, hmI] until [sfd + 0xb8]
  all_goals exact topSt_congr hSt rfl rfl rfl rfl rfl rfl rfl

open Janus.Contracts.Cmpstring in
/-- at the `cmpstring` call: what the continuation needs -/
def CmpCtx (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s Sc : State) : Prop :=
  CallSt R R2 T b L lo hi z pS s Sc ∧ Sc.mem.readLE ((s.regs 4).toNat - 72) 8 = 4933285 ∧
    Sc.mem.readLE ((s.regs 4).toNat - 24) 8 = 78 ∧
    Sc.mem.readLE ((s.regs 4).toNat - 16) 8 = pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
    Sc.regs 0 = pS + BitVec.ofNat 64 (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
    Sc.regs 1 = BitVec.ofNat 64 extCfg.maxStr ∧ Sc.regs 3 = 78#64 ∧ Sc.regs 7 = 78#64 ∧
    nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = 78

open Janus.Contracts.Cmpstring in
theorem c3a_post (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (S Sc : State) (k : Nat) (hSt : TopSt R R2 T b L lo hi z pS s S)
    (hkq : k = startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)
    (heq : nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = 78)
    (h4 : Sc.regs 4 = s.regs 4 - 72#64) (h5 : Sc.regs 5 = S.regs 5) (h14 : Sc.regs 14 = S.regs 14) (hx : Sc.xmm 15 = S.xmm 15)
    (hdf : Sc.df = S.df) (hfs : Sc.fsBase = S.fsBase)
    (hm : Sc.mem = ((S.mem.writeLE ((s.regs 4).toNat - 16) 8 (pS.toNat + k)).writeLE ((s.regs 4).toNat - 24) 8 78).writeLE
      ((s.regs 4).toNat - 72) 8 4933285)
    (r0 : Sc.regs 0 = pS + BitVec.ofNat 64 k) (r1 : Sc.regs 1 = BitVec.ofNat 64 extCfg.maxStr)
    (r3 : Sc.regs 3 = 78#64) (r7 : Sc.regs 7 = 78#64) :
    CmpstringPre64 16 Sc ∧ CmpCtx R R2 T b L lo hi z pS nS s Sc := by
  obtain ⟨⟨hra1, hra2, hx15, hdf0⟩, h0', h3', h1', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hEnv0 := env_to hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv0
  have hnS := nS.isLt
  have hq := Fv256.TopMath.startPos_spec' (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hmf : MemFrame S.mem Sc.mem [(lo, hi)] := by
    rw [hm]
    repeat' first
      | exact MemFrame.refl _ _
      | refine MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  have hCall : CallSt R R2 T b L lo hi z pS s Sc := by
    refine callSt_of hMod.1 hSt (by omega) (by omega) h4 h5 h14 hx hdf hfs hmf (by omega) ?_ ?_ ?_ ?_ (by omega) (by omega)
    all_goals (rw [hm]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint])
  have hs72 : (Sc.regs 4).toNat = (s.regs 4).toNat - 72 := by rw [h4]; exact bv_sub_c _ 72 (by decide) (by omega)
  have hP : (pS + BitVec.ofNat 64 k).toNat = pS.toNat + k := add_toNat pS k (by simp only [Nat.reducePow]; omega)
  have h78 : (78#64 : BitVec 64).toNat = 78 := rfl
  have hmx : extCfg.maxStr = 5175732 := rfl
  have hmx2 : (BitVec.ofNat 64 extCfg.maxStr).toNat = extCfg.maxStr := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rw [hmx]; omega)
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, Or.inr ⟨?_, ?_⟩, Or.inr ⟨?_, ?_⟩⟩, hCall, ?_, ?_, ?_, by rw [r0, hkq], r1, r3, r7, heq⟩
  · rw [hs72, hm]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
    all_goals (try (rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; omega))
  · rw [hs72]; omega
  · rw [hs72]; omega
  · rw [hs72]; omega
  · rw [hmf.accessible, topSt_acc hSt, hs72]; exact Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  · rw [r0, hP, r3, h78, hmf.accessible, topSt_acc hSt]
    exact Arm64.Memory.accessible_mono _ (hp.resolve_left (by omega)) (by omega) (by omega)
  · rw [r0, hP, r3, h78]; omega
  · rw [r1, r7, h78, hmx2, hmf.accessible, topSt_acc hSt]; exact hMax
  · rw [r1, r7, h78, hmx2, hmx]; omega
  · rw [hm]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
    all_goals (try (rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; omega))
  · rw [hm]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    all_goals (try (rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; omega))
  · rw [hm]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl, hkq]; exact Nat.mod_eq_of_lt (by rw [← hkq]; omega)

open Janus.Contracts.Cmpstring in
set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- exactly 78 digits: spill and call `runtime.cmpstring` -/
theorem top_c3a (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 (sfd + 0x57)) (hM : TopMid R R2 T b L lo hi z pS nS s S)
    (heq : nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = 78) :
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (BitVec.ofNat 64 (Fv256.Amd64.SfdProg.program.contractAddr "runtime.cmpstring")) S
      (fun Sc => CmpstringPre64 16 Sc ∧ CmpCtx R R2 T b L lo hi z pS nS s Sc) := by
  have hpre' := hpre
  obtain ⟨hSt, h0, ⟨k, hk1, hk2, h3⟩, h1⟩ := hM
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0', h3', h1', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hEnv0 := env_to hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv0
  have hnS := nS.isLt
  have hsp := Fv256.TopMath.startPos_spec' (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hkq : k = startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := hk2 (by omega)
  have hmI := ofNat_toInt (nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (by omega)
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 64 := by rw [hSt.1]; exact bv_sub_c _ 64 (by decide) (by omega)
  have hwacc : S.mem.accessible ((s.regs 4).toNat - 72) 56 true = true := by
    rw [topSt_acc hSt]; exact Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  janus64_run [hpc, h1, hmI, hS4, heq, hwacc] until [Fv256.Amd64.SfdProg.program.contractAddr "runtime.cmpstring"]
  all_goals (
    refine ReachesRet.done (by first | rfl | decide) ?_
    refine c3a_post R R2 T b L lo hi z pS nS s hpre' S _ k hSt hkq heq ?h4 ?h5 ?h14 ?hx ?hdf ?hfs ?hm ?r0 ?r1 ?r3 ?r7
    case h4 => simp only [setRegF_apply]; simp [hSt.1]; bv_omega
    case h5 => simp [setRegF_apply]
    case h14 => simp [setRegF_apply]
    case hx => simp [setRegF_apply]
    case hdf => simp [setRegF_apply]
    case hfs => simp [setRegF_apply]
    case hm =>
      dsimp only
      have e1 : (s.regs 4).toNat - 64 + 48 = (s.regs 4).toNat - 16 := by omega
      have e2 : (s.regs 4).toNat - 64 + 40 = (s.regs 4).toNat - 24 := by omega
      have e3 : (s.regs 4).toNat - 64 - 8 = (s.regs 4).toNat - 72 := by omega
      rw [e1, e2, e3]
    case r0 => simp [setRegF_apply, h0, h3]
    case r1 => simp [setRegF_apply]; rfl
    case r3 => simp [setRegF_apply]
    case r7 => simp [setRegF_apply])

end Fv256.Amd64.SfdTop
