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

end Fv256.Amd64.SfdTop
