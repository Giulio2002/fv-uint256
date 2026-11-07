import Fv256.Amd64.SfdTopG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd
  Fv256.Amd64.SfdTopSpec Fv256.Amd64.SfdTopCfg Fv256.Amd64.SfdTopBr

namespace Fv256.Amd64.SfdTop

theorem topSt_of_callSt {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {z pS : BitVec 64}
    {s Sc S2 : State} (hL : R2.Laws) (hC : CallSt R R2 T b L lo hi z pS s Sc)
    (h4 : S2.regs 4 = s.regs 4 - 64#64) (h5 : S2.regs 5 = Sc.regs 5) (h14 : S2.regs 14 = Sc.regs 14)
    (hx : S2.xmm 15 = Sc.xmm 15) (hdf : S2.df = Sc.df) (hfs : S2.fsBase = Sc.fsBase)
    (hf : MemFrame Sc.mem S2.mem [(lo, hi)]) (hw : lo + 32 ≤ hi) (hlo : lo + 72 ≤ (s.regs 4).toNat) (hhi : (s.regs 4).toNat + 8 ≤ hi)
    (hsp : (s.regs 4).toNat < 2 ^ 64)
    (e1 : S2.mem.readLE ((s.regs 4).toNat - 8) 8 = Sc.mem.readLE ((s.regs 4).toNat - 8) 8)
    (e2 : S2.mem.readLE ((s.regs 4).toNat + 8) 8 = Sc.mem.readLE ((s.regs 4).toNat + 8) 8)
    (e3 : S2.mem.readLE ((s.regs 4).toNat + 16) 8 = Sc.mem.readLE ((s.regs 4).toNat + 16) 8)
    (e4 : S2.mem.readLE (s.regs 4).toNat 8 = Sc.mem.readLE (s.regs 4).toNat 8) :
    TopSt R R2 T b L lo hi z pS s S2 := by
  obtain ⟨a4, a5, a14, ax, adf, afs, amf, abp, az, ap, aret, aenv⟩ := hC
  have hs64 : (S2.regs 4).toNat = (s.regs 4).toNat - 64 := by rw [h4]; exact bv_sub_c _ 64 (by decide) (by omega)
  have hEnv := aenv
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18⟩ := aenv
  have hs72 : (Sc.regs 4).toNat = (s.regs 4).toNat - 72 := by rw [a4]; exact bv_sub_c _ 72 (by decide) (by omega)
  refine ⟨h4, h5.trans a5, h14.trans a14, hx.trans ax, hdf.trans adf, hfs.trans afs, ?_, e1.trans abp, e2.trans az, e3.trans ap,
    e4.trans aret, ?_⟩
  · exact MemFrame.trans amf hf (fun a n h => ⟨h, h⟩)
  · exact Env.frame0 hL hEnv ⟨by rw [hs64]; omega, by rw [hs64]; omega, by rw [hs64]; omega⟩ h14 hf hw

open Janus.Contracts.Cmpstring in
theorem cmp_after (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (Sc S'' : State) (hC : CmpCtx R R2 T b L lo hi z pS nS s Sc) (hpr : CmpstringPre64 16 Sc)
    (hret : CmpRet64 16 Sc S'') :
    TopSt R R2 T b L lo hi z pS s S'' ∧ S''.rip = BitVec.ofNat 64 4933285 ∧
      S''.regs 0 = BitVec.ofInt 64 (strCmp Sc.mem (pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) extCfg.maxStr 78 78) ∧
      S''.mem.readLE ((s.regs 4).toNat - 24) 8 = 78 ∧
      S''.mem.readLE ((s.regs 4).toNat - 16) 8 = pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
  obtain ⟨hCall, m72, m24, m16, r0, r1, r3, r7, heq⟩ := hC
  obtain ⟨junk, f, x, yh, m, zh, kr, hS, hf⟩ := hret
  obtain ⟨⟨hra1, hra2, hx15, hdf0⟩, h0', h3', h1', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hEnv0 := env_to hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv0
  have hC4 : Sc.regs 4 = s.regs 4 - 72#64 := hCall.1
  have hs72 : (Sc.regs 4).toNat = (s.regs 4).toNat - 72 := by rw [hC4]; exact bv_sub_c _ 72 (by decide) (by omega)
  have hfm : MemFrame Sc.mem m [(lo, hi)] := by
    refine hf.mono ?_
    intro a n h
    simp only [calleeStack64, outside_cons, outside_nil, and_true, hs72] at h ⊢
    omega
  have hrd : ∀ a, (a + 8 ≤ (s.regs 4).toNat - 88 ∨ (s.regs 4).toNat - 32 ≤ a) → (a + 8 ≤ (s.regs 4).toNat - 72 ∨ (s.regs 4).toNat - 64 ≤ a) →
      m.readLE a 8 = Sc.mem.readLE a 8 := by
    intro a h1 h2
    refine (hf.readLE a 8 ?_)
    simp only [calleeStack64, outside_cons, outside_nil, and_true, hs72]
    omega
  have hS4 : S''.regs 4 = s.regs 4 - 64#64 := by
    rw [hS]; simp only [retState64, callRegs64]; simp [hC4]; exact bv_72_8 _
  have hSt : TopSt R R2 T b L lo hi z pS s S'' := by
    refine topSt_of_callSt hMod.1 hCall hS4 ?_ ?_ ?_ ?_ ?_ (by rw [hS]; exact hfm) (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_ ?_
    · rw [hS]; simp [retState64, callRegs64]
    · rw [hS]; simp [retState64, callRegs64]
    · rw [hS]; simp [retState64, callRegs64]
    · rw [hS]; simp [retState64]
    · rw [hS]; simp [retState64]
    · rw [hS]; simp [retState64]; exact hrd _ (by omega) (by omega)
    · rw [hS]; simp [retState64]; exact hrd _ (by omega) (by omega)
    · rw [hS]; simp [retState64]; exact hrd _ (by omega) (by omega)
    · rw [hS]; simp [retState64]; exact hrd _ (by omega) (by omega)
  have hnS := nS.isLt
  have hq := Fv256.TopMath.startPos_spec' (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hP : (pS + BitVec.ofNat 64 (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)).toNat =
      pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := add_toNat pS _ (by simp only [Nat.reducePow]; omega)
  have h78 : (78#64 : BitVec 64).toNat = 78 := rfl
  have hmx : extCfg.maxStr = 5175732 := rfl
  have hmx2 : (BitVec.ofNat 64 extCfg.maxStr).toNat = extCfg.maxStr := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rw [hmx]; omega)
  refine ⟨hSt, ?_, ?_, ?_, ?_⟩
  · rw [hS]; simp only [retState64]
    show BitVec.ofNat 64 (Sc.mem.readLE (Sc.regs 4).toNat 8) = _
    rw [hs72, m72]
  · rw [hS]; simp only [retState64, callRegs64, cmpResult64]
    simp
    rw [r0, r1, r3, r7, hP, hmx2, h78]
  · rw [hS]; simp only [retState64]; rw [hrd _ (by omega) (by omega)]; exact m24
  · rw [hS]; simp only [retState64]; rw [hrd _ (by omega) (by omega)]; exact m16

open Janus.Contracts.Cmpstring in
theorem cmp_val (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (Sc : State) (hCall : CallSt R R2 T b L lo hi z pS s Sc)
    (heq : nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = 78) :
    strCmp Sc.mem (pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) extCfg.maxStr 78 78 = 1 ↔
      lexGt (fun j => Fv256.C.bytesAt s.mem pS.toNat (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) maxDigit 78 := by
  obtain ⟨⟨hra1, hra2, hx15, hdf0⟩, h0', h3', h1', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hq := Fv256.TopMath.startPos_spec' (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have cmf := hCall.2.2.2.2.2.2.1
  rw [Fv256.I.strCmp_eq_one_iff Sc.mem 78]
  refine Fv256.TopMath.lexGt_congr2 _ _ _ _ 78 (fun j hj => ?_) (fun j hj => ?_)
  · show Sc.mem.readLE (pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) 1 =
      s.mem.readLE (pS.toNat + (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1
    rw [Nat.add_assoc]
    exact cmf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; have := hpW.resolve_left (by omega); omega)
  · rw [← hMaxV j hj]
    refine cmf.readLE _ _ ?_
    have := hMaxo
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega

open Janus.Contracts.Cmpstring in
set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- `cmpstring` says the 78 digits are above `2^256 - 1`: `ErrBig256Range` -/
theorem top_c3_gt (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (Sc S'' : State) (hC : CmpCtx R R2 T b L lo hi z pS nS s Sc) (hpr : CmpstringPre64 16 Sc)
    (hret : CmpRet64 16 Sc S'')
    (hlex : lexGt (fun j => Fv256.C.bytesAt s.mem pS.toNat (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) maxDigit 78) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S'' (TopPost extCfg R R2 T b L lo hi z pS nS s) := by
  have hpre' := hpre
  have heq := hC.2.2.2.2.2.2.2.2
  obtain ⟨hSt, hpc, hR0, m24, m16⟩ := cmp_after R R2 T b L lo hi z pS nS s hpre Sc S'' hC hpr hret
  have hv := (cmp_val R R2 T b L lo hi z pS nS s hpre Sc hC.1 heq).2 hlex
  have hR0' : S''.regs 0 = 1#64 := by rw [hR0, hv]; rfl
  have h1 : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (sfd + 0x8a)) S'' (TopSt R R2 T b L lo hi z pS s) := by
    have hm1 : ¬ (1#64).msb = true := by decide
    janus64_run [hpc, hR0', hm1] until [sfd + 0x8a]
    all_goals exact topSt_congr hSt rfl rfl rfl rfl rfl rfl rfl
  refine Fv256.SegCompose.seg_trans h1 (fun S3 hpc3 hSt3 => top_range impl R R2 T b L lo hi z pS nS s hpre' S3 (sfd + 0x8a) (Or.inr rfl) hpc3 hSt3 ?_)
  exact Fv256.TopMath.decParse_gt78 _ _ heq hlex

open Janus.Contracts.Cmpstring in
set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- `cmpstring` says the 78 digits are at most `2^256 - 1`: reload and call `fromDecimal` -/
theorem top_c3_le (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (Sc S'' : State) (hC : CmpCtx R R2 T b L lo hi z pS nS s Sc) (hpr : CmpstringPre64 16 Sc)
    (hret : CmpRet64 16 Sc S'')
    (hlex : ¬ lexGt (fun j => Fv256.C.bytesAt s.mem pS.toNat (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) maxDigit 78) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 Fv256.Amd64.SfdFd.fd) S''
      (fun S3 => FdPre R R2 T b L lo ((s.regs 4).toNat - 40) z (S3.regs 3) (S3.regs 1) S3 ∧
        FdCtx R R2 T b L lo hi z pS nS s 4933330 S3) := by
  have hpre' := hpre
  have heq := hC.2.2.2.2.2.2.2.2
  obtain ⟨hSt, hpc, hR0, m24, m16⟩ := cmp_after R R2 T b L lo hi z pS nS s hpre Sc S'' hC hpr hret
  have hv := cmp_val R R2 T b L lo hi z pS nS s hpre Sc hC.1 heq
  have hne : strCmp Sc.mem (pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) extCfg.maxStr 78 78 ≠ 1 :=
    fun h => hlex (hv.1 h)
  have hcases := strCmp_cases Sc.mem (pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) extCfg.maxStr 78 78
  have hR0v : S''.regs 0 = 0#64 ∨ S''.regs 0 = 18446744073709551615#64 := by
    rw [hR0]
    rcases hcases with h | h | h
    · right; rw [h]; decide
    · left; rw [h]; decide
    · exact absurd h hne
  obtain ⟨⟨hra1, hra2, hx15, hdf0⟩, h0', h3', h1', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hEnv0 := env_to hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv0
  have hnS := nS.isLt
  have hq := Fv256.TopMath.startPos_spec' (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hS4 : (S''.regs 4).toNat = (s.regs 4).toNat - 64 := by rw [hSt.1]; exact bv_sub_c _ 64 (by decide) (by omega)
  have hz8 : S''.mem.readLE ((s.regs 4).toNat - 64 + 72) 8 = z.toNat := by
    have e : (s.regs 4).toNat - 64 + 72 = (s.regs 4).toNat + 8 := by omega
    rw [e]; exact hSt.2.2.2.2.2.2.2.2.1
  have m24' : S''.mem.readLE ((s.regs 4).toNat - 64 + 40) 8 = 78 := by
    have e : (s.regs 4).toNat - 64 + 40 = (s.regs 4).toNat - 24 := by omega
    rw [e]; exact m24
  have m16' : S''.mem.readLE ((s.regs 4).toNat - 64 + 48) 8 = pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
    have e : (s.regs 4).toNat - 64 + 48 = (s.regs 4).toNat - 16 := by omega
    rw [e]; exact m16
  have hrd : S''.mem.accessible ((s.regs 4).toNat - 72) 56 true = true := by
    rw [hSt.2.2.2.2.2.2.1.accessible]; exact Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  have hr : S''.mem.accessible ((s.regs 4).toNat - 64) 80 false = true := by
    rw [hSt.2.2.2.2.2.2.1.accessible]; exact Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ e5 (by omega) (by omega))
  have hmm1 : (18446744073709551615#64 : BitVec 64).msb = true := by decide
  rcases hR0v with hv0 | hv0
  all_goals
    janus64_run [hpc, hv0, hS4, hz8, m24', m16', hrd, hr, hmm1] until [Fv256.Amd64.SfdFd.fd]
    all_goals (
      refine c1_post R R2 T b L lo hi z pS nS s hpre' S'' _ (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) 78 4933330 _ _ ?hp ?hn hSt ?h4 ?h5 ?h14 ?hx ?hdf ?hfs ?hm (by decide) ?r0 ?r3 ?r1
        (by omega) (by omega) ?hfin (Nat.le_refl _) (fun _ => rfl) heq.symm
      case hp =>
        have hpk : pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < 2 ^ 64 := by omega
        rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      case hn => rfl
      case h4 => simp only [setRegF_apply]; simp [hSt.1]; bv_omega
      case h5 => simp [setRegF_apply]
      case h14 => simp [setRegF_apply]
      case hx => simp [setRegF_apply]
      case hdf => simp [setRegF_apply]
      case hfs => simp [setRegF_apply]
      case hm =>
        dsimp only
        have e : (s.regs 4).toNat - 64 - 8 = (s.regs 4).toNat - 72 := by omega
        rw [e]
      case r0 => simp [setRegF_apply]
      case r3 =>
        simp only [setRegF_apply]; simp
        rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      case r1 => simp [setRegF_apply]
      case hfin =>
        intro hd
        have hx : lexGt (Fv256.C.bytesAt s.mem (pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)) maxDigit 78 ↔
            lexGt (fun j => Fv256.C.bytesAt s.mem pS.toNat (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) maxDigit 78 :=
          Fv256.TopMath.lexGt_congr2 _ _ _ _ 78 (fun j _ => by
            show s.mem.readLE (pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) 1 =
              s.mem.readLE (pS.toNat + (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1
            rw [Nat.add_assoc]) (fun j _ => rfl)
        have hdm : allDec maxDigit 0 78 := fun k _ hk => Fv256.I.Fv256.I.maxDigit_isDec k hk
        have := (Fv256.I.Fv256.I.lexGt_iff 78 _ maxDigit hd hdm)
        have h2 : ¬ lexGt (Fv256.C.bytesAt s.mem (pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)) maxDigit 78 :=
          fun h => hlex (hx.1 h)
        rw [this] at h2
        have h3 := Fv256.I.Fv256.I.decSum_maxDigit
        omega)

end Fv256.Amd64.SfdTop
