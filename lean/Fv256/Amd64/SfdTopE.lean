import Fv256.Amd64.SfdTopD

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd
  Fv256.Amd64.SfdTopSpec Fv256.Amd64.SfdTopCfg Fv256.Amd64.SfdTopBr

namespace Fv256.Amd64.SfdTop

theorem bytes_congr (m m' : Janus.Arm64.Memory) (p n : Nat) (h : ∀ j, j < n → m'.readLE (p + j) 1 = m.readLE (p + j) 1) :
    (allDec (Fv256.C.bytesAt m' p) 0 n ↔ allDec (Fv256.C.bytesAt m p) 0 n) ∧
      decSum (Fv256.C.bytesAt m' p) 0 n = decSum (Fv256.C.bytesAt m p) 0 n := by
  refine ⟨?_, decSum_congr _ _ 0 n (fun k _ hk => h k (by omega))⟩
  unfold allDec
  constructor
  · intro H k h1 h2; have := H k h1 h2; simpa [Fv256.C.bytesAt, h k h2] using this
  · intro H k h1 h2; have := H k h1 h2; simpa [Fv256.C.bytesAt, h k h2] using this

theorem multOK_frame (C : SfdCfg) {z lo hi : Nat} {m m' : Janus.Arm64.Memory} (hf : MemFrame m m' [(lo, hi)])
    (h : MultOK C z lo hi m) : MultOK C z lo hi m' := by
  obtain ⟨a, o, H⟩ := h
  have o' := o
  simp only [outside_cons, outside_nil, and_true] at o'
  refine ⟨by rw [hf.accessible]; exact a, o, fun k hk1 hk2 => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := H k hk1 hk2
  have h4' := h4
  simp only [outside_cons, outside_nil, and_true] at h4'
  have e1 : m'.readLE (C.mulTab + 8 * k) 8 = m.readLE (C.mulTab + 8 * k) 8 :=
    hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  rw [e1, hf.accessible]
  refine ⟨h1, h2, ?_, h4⟩
  unfold Janus.Spec.val256 at h3 ⊢
  rw [hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact h3

theorem outside_hi {a n lo hi hi' z : Nat} (h : Outside a n [(lo, hi), (z, z + 32)]) (hh : hi' ≤ hi) :
    Outside a n [(lo, hi'), (z, z + 32)] := by
  simp only [outside_cons, outside_nil, and_true] at h ⊢
  omega

theorem multOK_hi (C : SfdCfg) {z lo hi hi' : Nat} {m : Janus.Arm64.Memory} (h : MultOK C z lo hi m) (hh : hi' ≤ hi) :
    MultOK C z lo hi' m := by
  obtain ⟨a, o, H⟩ := h
  refine ⟨a, outside_hi o hh, fun k hk1 hk2 => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := H k hk1 hk2
  exact ⟨h1, h2, h3, outside_hi h4 hh⟩

theorem chunkAll_hi (C : SfdCfg) {R : RtInv} {R2 : IfaceModel} {L : List (Nat × Nat)} {b pS nS lo hi hi' : Nat}
    {m : Janus.Arm64.Memory} (h : ChunkAll C R R2 L b pS nS lo hi m) (hh : hi' ≤ hi) : ChunkAll C R R2 L b pS nS lo hi' m := by
  intro sp sl hs1 hs2 hl1 hl2
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := h sp sl hs1 hs2 hl1 hl2
  exact ⟨c1, c2, c3, c4, c5, by omega, c7, c8⟩

theorem chunkAll_frame (C : SfdCfg) {R : RtInv} {R2 : IfaceModel} {L : List (Nat × Nat)} {b pS nS lo hi : Nat}
    {m m' : Janus.Arm64.Memory} (hf : MemFrame m m' [(lo, hi)]) (h : ChunkAll C R R2 L b pS nS lo hi m)
    {pS' nS' : Nat} (h1 : pS ≤ pS') (h2 : pS' + nS' ≤ pS + nS) : ChunkAll C R R2 L b pS' nS' lo hi m' := by
  intro sp sl hs1 hs2 hl1 hl2
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := h sp sl (by omega) (by omega) hl1 hl2
  exact ⟨c1, c2, c3, by rw [hf.accessible]; exact c4, c5, c6, c7, c8⟩

theorem fdpre_of (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (Sc : State) (k len : Nat) (hmf : MemFrame s.mem Sc.mem [(lo, hi)])
    (hEnvSc : Fv256.Amd64.SfdEnv.Env R R2 T b L lo hi Sc)
    (h4 : Sc.regs 4 = s.regs 4 - 72#64) (h14 : Sc.regs 14 = s.regs 14) (hret : Fv256.C.RetOK Sc)
    (hk : k + len ≤ nS.toNat) (hlen : len ≤ 78)
    (r0 : Sc.regs 0 = z) (r3 : Sc.regs 3 = pS + BitVec.ofNat 64 k) (r1 : Sc.regs 1 = BitVec.ofNat 64 len)
    (hfin : allDec (Fv256.C.bytesAt s.mem (pS.toNat + k)) 0 len →
      decSum (Fv256.C.bytesAt s.mem (pS.toNat + k)) 0 len < 2 ^ 256) :
    FdPre R R2 T b L lo ((s.regs 4).toNat - 40) z (pS + BitVec.ofNat 64 k) (BitVec.ofNat 64 len) Sc := by
  obtain ⟨_, h0', h3', h1', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hEnv0 := env_to hEnv
  have hEnv' := hEnv0
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hnS := nS.isLt
  have hs72 : (Sc.regs 4).toNat = (s.regs 4).toNat - 72 := by rw [h4]; exact bv_sub_c _ 72 (by decide) (by omega)
  have hpk : (pS + BitVec.ofNat 64 k).toNat = pS.toNat + k := add_toNat pS k (by simp only [Nat.reducePow]; omega)
  have hlN : (BitVec.ofNat 64 len).toNat = len := by simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  refine ⟨hret, r0, r3, r1, by rw [hlN]; exact hlen, mod_to hMod, ?_, by rw [hs72]; omega, by rw [hs72]; omega, ?_, ?_, ?_, ?_, ?_,
    hzR, hzP, hzS, (by rw [h14]; exact hzg), ⟨by rw [hpk, hlN]; omega, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact Env.shrink hEnvSc (Nat.le_refl _) (by omega) (by rw [hs72]; omega) (by rw [hs72]; omega)
  · exact mult_to (multOK_hi extCfg (multOK_frame extCfg hmf hMult) (by omega))
  · rw [hmf.accessible]; exact hEOF
  · exact outside_hi hEOFo (by omega)
  · exact ⟨hzw, by rw [hmf.accessible]; exact hz⟩
  · omega
  · by_cases hl0 : len = 0
    · left; rw [hlN]; exact hl0
    · right; rw [hpk, hlN, hmf.accessible]
      exact Arm64.Memory.accessible_mono _ (hp.resolve_left (by omega)) (by omega) (by omega)
  · by_cases hl0 : len = 0
    · left; rw [hlN]; exact hl0
    · right; rw [hpk, hlN]
      have := hpW.resolve_left (by omega)
      omega
  · by_cases hl0 : len = 0
    · left; rw [hlN]; exact hl0
    · right; rw [hpk, hlN]
      have := hpz.resolve_left (by omega)
      omega
  · rw [hpk, hlN]
    exact chunk_to (chunkAll_hi extCfg (chunkAll_frame extCfg hmf hCA (by omega) (by omega)) (by omega))
  · intro hd
    have hbc := bytes_congr s.mem Sc.mem (pS.toNat + k) len (fun j hj =>
      hmf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; have := hpW.resolve_left (by omega); omega))
    rw [hpk, hlN] at *
    exact hbc.2 ▸ hfin (hbc.1.1 hd)

/-- the state at the `fromDecimal` call (return slot at `sp0 - 72`): the frame facts of `TopSt` with the stack pointer 8 lower -/
def CallSt (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS : BitVec 64)
    (s Sc : State) : Prop :=
  Sc.regs 4 = s.regs 4 - 72#64 ∧ Sc.regs 5 = s.regs 4 - 8#64 ∧ Sc.regs 14 = s.regs 14 ∧ Sc.xmm 15 = 0 ∧ Sc.df = false ∧
  Sc.fsBase = s.fsBase ∧ MemFrame s.mem Sc.mem [(lo, hi)] ∧
  Sc.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧
  Sc.mem.readLE ((s.regs 4).toNat + 8) 8 = z.toNat ∧ Sc.mem.readLE ((s.regs 4).toNat + 16) 8 = pS.toNat ∧
  Sc.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 ∧
  Fv256.Amd64.SfdEnv.Env R R2 T b L lo hi Sc

theorem callSt_of {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {z pS : BitVec 64}
    {s S Sc : State} (hL : R2.Laws) (hS : TopSt R R2 T b L lo hi z pS s S) (hlo : 72 ≤ (s.regs 4).toNat)
    (hsp : (s.regs 4).toNat < 2 ^ 64)
    (h4 : Sc.regs 4 = s.regs 4 - 72#64) (h5 : Sc.regs 5 = S.regs 5) (h14 : Sc.regs 14 = S.regs 14) (hx : Sc.xmm 15 = S.xmm 15)
    (hdf : Sc.df = S.df) (hfs : Sc.fsBase = S.fsBase) (hf : MemFrame S.mem Sc.mem [(lo, hi)]) (hw : lo + 32 ≤ hi)
    (e1 : Sc.mem.readLE ((s.regs 4).toNat - 8) 8 = S.mem.readLE ((s.regs 4).toNat - 8) 8)
    (e2 : Sc.mem.readLE ((s.regs 4).toNat + 8) 8 = S.mem.readLE ((s.regs 4).toNat + 8) 8)
    (e3 : Sc.mem.readLE ((s.regs 4).toNat + 16) 8 = S.mem.readLE ((s.regs 4).toNat + 16) 8)
    (e4 : Sc.mem.readLE (s.regs 4).toNat 8 = S.mem.readLE (s.regs 4).toNat 8)
    (hlo2 : lo + 72 ≤ (s.regs 4).toNat) (hhi : (s.regs 4).toNat + 8 ≤ hi) :
    CallSt R R2 T b L lo hi z pS s Sc := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hS
  have hEnv := a12
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18⟩ := a12
  have hs72 : (Sc.regs 4).toNat = (s.regs 4).toNat - 72 := by rw [h4]; exact bv_sub_c _ 72 (by decide) hlo
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 64 := by rw [a1]; exact bv_sub_c _ 64 (by decide) (by omega)
  refine ⟨h4, h5.trans a2, h14.trans a3, hx.trans a4, hdf.trans a5, hfs.trans a6, ?_, e1.trans a8, e2.trans a9, e3.trans a10,
    e4.trans a11, ?_⟩
  · exact MemFrame.trans a7 hf (fun a n h => ⟨h, h⟩)
  · exact Env.frame0 hL hEnv ⟨by rw [hs72]; omega, by rw [hs72]; omega, by rw [hs72]; omega⟩ h14 hf hw

/-- at a `fromDecimal` call: what the continuation needs -/
def FdCtx (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s : State) (ret : Nat) (Sc : State) : Prop :=
  CallSt R R2 T b L lo hi z pS s Sc ∧ Sc.regs 0 = z ∧
    (∃ k, k ≤ startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
      (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < nS.toNat → k = startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
      Sc.regs 3 = pS + BitVec.ofNat 64 k) ∧
    Sc.regs 1 = BitVec.ofNat 64 (nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
    Sc.mem.readLE ((s.regs 4).toNat - 72) 8 = ret

theorem c1_post (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (S Sc : State) (k len ret : Nat) (hSt : TopSt R R2 T b L lo hi z pS s S)
    (h4 : Sc.regs 4 = s.regs 4 - 72#64) (h5 : Sc.regs 5 = S.regs 5) (h14 : Sc.regs 14 = S.regs 14) (hx : Sc.xmm 15 = S.xmm 15)
    (hdf : Sc.df = S.df) (hfs : Sc.fsBase = S.fsBase) (hm : Sc.mem = S.mem.writeLE ((s.regs 4).toNat - 72) 8 ret)
    (hret : ret < 2 ^ 47) (r0 : Sc.regs 0 = z) (r3 : Sc.regs 3 = pS + BitVec.ofNat 64 k) (r1 : Sc.regs 1 = BitVec.ofNat 64 len)
    (hk : k + len ≤ nS.toNat) (hlen : len ≤ 78)
    (hfin : allDec (Fv256.C.bytesAt s.mem (pS.toNat + k)) 0 len →
      decSum (Fv256.C.bytesAt s.mem (pS.toNat + k)) 0 len < 2 ^ 256)
    (hq1 : k ≤ startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)
    (hq2 : startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < nS.toNat → k = startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)
    (hlq : len = nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) :
    FdPre R R2 T b L lo ((s.regs 4).toNat - 40) z (pS + BitVec.ofNat 64 k) (BitVec.ofNat 64 len) Sc ∧
      FdCtx R R2 T b L lo hi z pS nS s ret Sc := by
  have hpre' := hpre
  obtain ⟨⟨hra1, hra2, hx15, hdf0⟩, h0', h3', h1', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hEnv0 := env_to hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv0
  have hmf : MemFrame S.mem Sc.mem [(lo, hi)] := by
    rw [hm]
    refine MemFrame.writeLE (MemFrame.refl _ _) _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  have hCall : CallSt R R2 T b L lo hi z pS s Sc := by
    refine callSt_of hMod.1 hSt (by omega) (by omega) h4 h5 h14 hx hdf hfs hmf (by omega) ?_ ?_ ?_ ?_ (by omega) (by omega)
    all_goals (rw [hm]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint])
  have hs72 : (Sc.regs 4).toNat = (s.regs 4).toNat - 72 := by rw [h4]; exact bv_sub_c _ 72 (by decide) (by omega)
  have hretOK : Fv256.C.RetOK Sc := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hs72, hCall.2.2.2.2.2.2.1.accessible]
      exact Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ e5 (by omega) (by omega))
    · rw [hs72, hm]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
      rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt (by omega)]; exact hret
    · rw [hx]; exact hSt.2.2.2.1
    · rw [hdf]; exact hSt.2.2.2.2.1
  refine ⟨fdpre_of R R2 T b L lo hi z pS nS s hpre' Sc k len (MemFrame.trans hSt.2.2.2.2.2.2.1 hmf (fun a n h => ⟨h, h⟩)) hCall.2.2.2.2.2.2.2.2.2.2.2 h4 (by rw [h14, hSt.2.2.1]) hretOK hk hlen r0 r3 r1 hfin, hCall, r0, ⟨k, hq1, hq2, r3⟩, ?_, ?_⟩
  · rw [r1, hlq]
  · rw [hm]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
    rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (by omega)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- fewer than 78 digits: call `fromDecimal` -/
theorem top_c1 (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 (sfd + 0x57)) (hM : TopMid R R2 T b L lo hi z pS nS s S)
    (hlt : nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < 78) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 Fv256.Amd64.SfdFd.fd) S
      (fun Sc => FdPre R R2 T b L lo ((s.regs 4).toNat - 40) z (Sc.regs 3) (Sc.regs 1) Sc ∧
        FdCtx R R2 T b L lo hi z pS nS s 4933361 Sc) := by
  have hpre' := hpre
  obtain ⟨hSt, h0, ⟨k, hk1, hk2, h3⟩, h1⟩ := hM
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0', h3', h1', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hEnv0 := env_to hEnv
  have hnS := nS.isLt
  have hsp := Fv256.TopMath.startPos_spec' (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hmI := ofNat_toInt (nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (by omega)
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 64 := by rw [hSt.1]; exact bv_sub_c _ 64 (by decide) (by omega)
  janus64_run [hpc, h1, hmI, hS4] until [Fv256.Amd64.SfdFd.fd]
  all_goals (
    refine c1_post R R2 T b L lo hi z pS nS s hpre' S _ k _ 4933361 hSt ?h4 ?h5 ?h14 ?hx rfl rfl rfl (by decide) ?r0 ?r3 ?r1
      (by omega) (by omega) ?hfin hk1 hk2 rfl
    case h4 => simp only [setRegF_apply]; simp [hSt.1]; bv_omega
    case h5 => simp [setRegF_apply]
    case h14 => simp [setRegF_apply]
    case hx => simp [setRegF_apply]
    case r0 => simp [setRegF_apply, h0]
    case r3 => simp [setRegF_apply, h3]
    case r1 => simp [setRegF_apply, h1]
    case hfin =>
      intro hd
      have := decSum_lt (Fv256.C.bytesAt s.mem (pS.toNat + k)) 0 (nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (by simpa using hd)
      have h10 : 10 ^ (nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ≤ 10 ^ 77 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have := Fv256.I.Fv256.I.pow77_lt
      omega)

end Fv256.Amd64.SfdTop
