import Fv256.Arm64.SfdTopB
import Fv256.Arm64.SfdFdF

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdTopSpec

namespace Fv256.Arm64.SfdTop

section Defs
variable (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
  (s : State)

/-- at a `fromDecimal` call: what the continuation needs -/
def FdCtx (ret : Nat) (S : State) : Prop :=
  TopSt R R2 T b L lo hi z pS s S ∧ S.regs 30 = BitVec.ofNat 64 ret ∧ S.regs 0 = z ∧
    (∃ k, k ≤ startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
      (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < nS.toNat → k = startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
      S.regs 1 = pS + BitVec.ofNat 64 k) ∧
    S.regs 2 = BitVec.ofNat 64 (nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)

/-- at the `cmpstring` call: what the continuation needs -/
def CmpCtx (S : State) : Prop :=
  TopSt R R2 T b L lo hi z pS s S ∧ S.regs 30 = BitVec.ofNat 64 0xb8a44 ∧
    S.mem.readLE (S.sp.toNat + 56) 8 = 78 ∧
    S.mem.readLE (S.sp.toNat + 64) 8 = pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
    S.regs 0 = pS + BitVec.ofNat 64 (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
    S.regs 1 = 78#64 ∧ S.regs 2 = BitVec.ofNat 64 cfg.maxStr ∧ S.regs 3 = 78#64 ∧
    nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = 78

end Defs

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
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S' : State) (k len : Nat) (hSt : TopSt R R2 T b L lo hi z pS s S')
    (hk : k + len ≤ nS.toNat) (hlen : len ≤ 78)
    (r0 : S'.regs 0 = z) (r1 : S'.regs 1 = pS + BitVec.ofNat 64 k) (r2 : S'.regs 2 = BitVec.ofNat 64 len)
    (hl1 : (S'.regs 30).toNat % 4 = 0) (hl2 : (S'.regs 30).toNat < 2 ^ 48)
    (hfin : allDec (Fv256.C.bytesAt s.mem (pS.toNat + k)) 0 len →
      decSum (Fv256.C.bytesAt s.mem (pS.toNat + k)) 0 len < 2 ^ 256) :
    Fv256.Arm64.SfdFd.FdPre R R2 T b L lo (s.sp.toNat - 48) z (pS + BitVec.ofNat 64 k) (BitVec.ofNat 64 len) S' := by
  have hSt0 := hSt
  obtain ⟨_, _, _, _, hmf, _⟩ := hSt0
  obtain ⟨_, _, h0', h1', h2', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  have hEnv0 := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv0
  have hnS := nS.isLt
  have hspS := topSt_sp hSt (by omega)
  have hpk : (pS + BitVec.ofNat 64 k).toNat = pS.toNat + k := add_toNat pS k (by simp only [Nat.reducePow]; omega)
  have hlN : (BitVec.ofNat 64 len).toNat = len := by simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  have hf := hmf
  have hEnvS := hSt.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨hl1, hl2, r0, r1, r2, by rw [hlN]; exact hlen, hMod, ?_, by rw [hspS]; omega,
    by rw [hspS]; omega, ?_, ?_, ?_, ?_, by omega, hzR, hzP, hzS, (by rw [hSt.2.2.1]; exact hzg), ?_,
    by rw [hpk, hlN]; omega, ?_, ?_, ?_, ?_⟩
  · exact Fv256.Arm64.SfdEnv.Env.shrink hEnvS (Nat.le_refl _) (by omega) (by rw [hspS]; omega) (by rw [hspS]; omega)
  · exact multOK_hi cfg (multOK_frame cfg hf hMult) (by omega)
  · rw [hf.accessible]; exact hEOF
  · exact outside_hi hEOFo (by omega)
  · exact ⟨by rw [hf.accessible]; exact hz.1, hz.2⟩
  · rw [hpk, hlN]
    by_cases hl0 : len = 0
    · exact Or.inl hl0
    · refine Or.inr ?_
      rw [hf.accessible]
      exact Arm64.Memory.accessible_mono _ (hpA.resolve_left (by omega)) (by omega) (by omega)
  · rw [hpk, hlN]; omega
  · rw [hpk, hlN]; omega
  · exact chunkAll_hi cfg (chunkAll_frame cfg hf hCA (by omega) (by rw [hlN]; omega)) (by omega)
  · intro hd
    have hbc := bytes_congr s.mem S'.mem (pS.toNat + k) len (fun j hj =>
      hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega))
    rw [hpk, hlN] at *
    exact hbc.2 ▸ hfin (hbc.1.1 hd)

theorem call_post (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S S' : State) (k len ret : Nat) (hSt : TopSt R R2 T b L lo hi z pS s S)
    (hsp : S'.sp = S.sp) (h29 : S'.regs 29 = S.regs 29) (h28 : S'.regs 28 = S.regs 28) (h18 : S'.regs 18 = S.regs 18)
    (hmem : S'.mem = S.mem) (r0 : S'.regs 0 = z) (r1 : S'.regs 1 = pS + BitVec.ofNat 64 k)
    (r2 : S'.regs 2 = BitVec.ofNat 64 len) (r30 : S'.regs 30 = BitVec.ofNat 64 ret)
    (hret1 : ret % 4 = 0) (hret2 : ret < 2 ^ 48) (hk : k + len ≤ nS.toNat) (hlen : len ≤ 78)
    (hfin : allDec (Fv256.C.bytesAt s.mem (pS.toNat + k)) 0 len →
      decSum (Fv256.C.bytesAt s.mem (pS.toNat + k)) 0 len < 2 ^ 256)
    (hq1 : k ≤ startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)
    (hq2 : startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < nS.toNat → k = startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)
    (hlq : len = nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) :
    Fv256.Arm64.SfdFd.FdPre R R2 T b L lo (s.sp.toNat - 48) z (S'.regs 1) (S'.regs 2) S' ∧
      FdCtx R R2 T b L lo hi z pS nS s ret S' := by
  have hSt' : TopSt R R2 T b L lo hi z pS s S' := by
    obtain ⟨hl1, hl2, h0', h1', h2', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
    exact topSt_step hMod.1 hSt (by have := hEnv.1; omega) hsp h29 h28 h18 (by rw [hmem]; exact MemFrame.refl _ _)
      (by omega) (by rw [hmem]) (by rw [hmem]) (by rw [hmem]) (by rw [hmem]) (by rw [hmem]) (by rw [hmem])
  have hl1 : (S'.regs 30).toNat % 4 = 0 := by
    rw [r30]; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  have hl2 : (S'.regs 30).toNat < 2 ^ 48 := by
    rw [r30]; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  refine ⟨?_, hSt', r30, r0, ⟨k, hq1, hq2, r1⟩, ?_⟩
  · rw [r1, r2]; exact fdpre_of R R2 T b L lo hi z pS nS s hpre S' k len hSt' hk hlen r0 r1 r2 hl1 hl2 hfin
  · rw [r2, hlq]

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- fewer than 78 digits: call `fromDecimal` -/
theorem top_c1 (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 0xb8a18) (hM : TopMid R R2 T b L lo hi z pS nS s S)
    (hlt : nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < 78) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (BitVec.ofNat 64 Fv256.Arm64.SfdFd.fd) S
      (fun S' => Fv256.Arm64.SfdFd.FdPre R R2 T b L lo (s.sp.toNat - 48) z (S'.regs 1) (S'.regs 2) S' ∧
        FdCtx R R2 T b L lo hi z pS nS s 0xb8a9c S') := by
  have hpre' := hpre
  obtain ⟨hSt, h0, ⟨k, hk1, hk2, h1⟩, h2⟩ := hM
  have hnS := nS.isLt
  have hsp := Fv256.TopMath.startPos_spec' (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hmI := ofNat_toInt (nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (by omega)
  janus_run [hpc, h2, hmI] until [0xb8b50]
  have hlen78 : nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ≤ 78 := by omega
  have hq := Fv256.TopMath.startPos_spec' (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  all_goals (
    refine ReachesRet.done (by first | rfl | decide) ?_
    exact call_post R R2 T b L lo hi z pS nS s hpre' S _ k _ 0xb8a9c hSt rfl (by simp [setReg_apply]) (by simp [setReg_apply])
      (by simp [setReg_apply]) rfl (by simp [setReg_apply, h0]) (by simp [setReg_apply, h1]) (by simp [setReg_apply, h2])
      (by simp [setReg_apply]) (by omega) (by omega) (by omega) hlen78 (fun hd => by
        have := decSum_lt (Fv256.C.bytesAt s.mem (pS.toNat + k)) 0 (nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (by simpa using hd)
        have h10 : 10 ^ (nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ≤ 10 ^ 77 :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have := Fv256.I.Fv256.I.pow77_lt
        omega) hk1 hk2 rfl)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- the epilogue: reload FP and LR, pop the frame, return -/
theorem top_epi (impl : List Segment) (s S1 : State) (pcE : Nat) (hE : pcE = 0xb8a9c ∨ pcE = 0xb8a74)
    (hpc : S1.pc = BitVec.ofNat 64 pcE) (hsp : S1.sp + 80#64 = s.sp) (hal : S1.sp.toNat % 16 = 0) (h8 : 8 ≤ S1.sp.toNat) (hl2 : (s.regs 30).toNat < 2 ^ 48) (hl1 : (s.regs 30).toNat % 4 = 0)
    (hx29 : S1.mem.readLE (S1.sp.toNat - 8) 8 = (s.regs 29).toNat)
    (hx30 : S1.mem.readLE S1.sp.toNat 8 = (s.regs 30).toNat)
    (hacc : S1.mem.accessible (S1.sp.toNat - 8) 16 false = true) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (s.regs 30) S1
      (fun S2 => S2.sp = s.sp ∧ S2.regs 29 = s.regs 29 ∧ S2.regs 0 = S1.regs 0 ∧ S2.regs 1 = S1.regs 1 ∧
        S2.regs 28 = S1.regs 28 ∧ S2.regs 18 = S1.regs 18 ∧ S2.mem = S1.mem) := by
  have hret : BitVec.ofNat 64 (S1.mem.readLE S1.sp.toNat 8) = s.regs 30 := by
    rw [hx30]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)
  have h29 : BitVec.ofNat 64 (S1.mem.readLE (S1.sp.toNat - 8) 8) = s.regs 29 := by
    rw [hx29]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)
  rcases hE with rfl | rfl
  · janus_run [hpc, hret, h29, hacc, hx29, hx30, hsp, hal, h8, hl2, hl1]
  · janus_run [hpc, hret, h29, hacc, hx29, hx30, hsp, hal, h8, hl2, hl1]

open Fv256.Arm64.SegCompose in
set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- after `fromDecimal` returns: the epilogue and the documented result -/
theorem top_fin (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (Sc S1 : State) (ret : Nat) (hret : ret = 0xb8a9c ∨ ret = 0xb8a74)
    (hC : FdCtx R R2 T b L lo hi z pS nS s ret Sc) (hpc : S1.pc = BitVec.ofNat 64 ret)
    (hpost : Fv256.Arm64.SfdFd.FdPost R R2 T b L lo (s.sp.toNat - 48) z (Sc.regs 1) (Sc.regs 2) Sc S1)
    (hdp : decParse (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat =
      fromDec (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (s.regs 30) S1
      (TopPost cfg R R2 T b L lo hi z pS nS s) := by
  have hpre' := hpre
  obtain ⟨hSt, r30, r0, ⟨k, hk1, hk2, r1⟩, r2⟩ := hC
  obtain ⟨p1, p29, p28, p18, hKeep, hcases⟩ := hpost
  obtain ⟨hl1, hl2, h0', h1', h2', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  have hEnv0 := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv0
  have hnS := nS.isLt
  have hspC := topSt_sp hSt (by omega)
  have hStV := hSt
  obtain ⟨t1, t2, t3, t4, tmf, tm1, tm2, tm3, tm4, tm5, tm6, tEnv⟩ := hStV
  have hq := Fv256.TopMath.startPos_spec' (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hS1sp : S1.sp.toNat = s.sp.toNat - 80 := by rw [p1]; exact hspC
  have hx29 : S1.mem.readLE (S1.sp.toNat - 8) 8 = (s.regs 29).toNat := by
    rw [show S1.sp.toNat - 8 = Sc.sp.toNat - 8 by rw [p1]]
    rw [hKeep.1, show Sc.sp.toNat - 8 = s.sp.toNat - 88 by omega]; exact tm2
  have hx30 : S1.mem.readLE S1.sp.toNat 8 = (s.regs 30).toNat := by
    rw [show S1.sp.toNat = Sc.sp.toNat by rw [p1]]
    rw [hKeep.2, show Sc.sp.toNat = s.sp.toNat - 80 by omega]; exact tm1
  have hspV : S1.sp + 80#64 = s.sp := by rw [p1, t1]; bv_omega
  have hacc : S1.mem.accessible (S1.sp.toNat - 8) 16 false = true := by
    have h0 : Sc.mem.accessible (S1.sp.toNat - 8) 16 false = true := by
      rw [hS1sp]
      have := tEnv
      obtain ⟨c1, c2, c3, c4, c5, _⟩ := this
      exact Arm64.Memory.accessible_mono _ (Arm64.Memory.accessible_weaken _ c5) (by omega) (by omega)
    rcases hcases with ⟨_, _, _, _, _, hf⟩ | ⟨v, _, _, _, _, _, hf⟩ | ⟨_, _, _, ⟨_, _, _, _, _, hf⟩⟩
    · rw [hf.accessible]; exact h0
    · rw [hf.accessible]; exact h0
    · rw [hf.accessible]; exact h0
  refine seg_mono (top_epi impl s S1 ret hret hpc hspV (by omega) (by omega) hl2 hl1 hx29 hx30 hacc) ?_
  intro S2 hS2
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hS2
  have pre : ∀ rs, MemFrame Sc.mem S1.mem rs → Outside (s.sp.toNat - 8) 16 rs →
      S2.sp = s.sp ∧ S2.regs 29 = s.regs 29 ∧ S2.regs 28 = s.regs 28 ∧ S2.regs 18 = s.regs 18 ∧
      S2.mem.readLE (s.sp.toNat - 8) 8 = s.mem.readLE (s.sp.toNat - 8) 8 ∧
      S2.mem.readLE s.sp.toNat 8 = s.mem.readLE s.sp.toNat 8 := by
    intro rs hf hOut
    refine ⟨q1, q2, q5.trans (p28.trans t3), q6.trans (p18.trans t4), ?_, ?_⟩
    · rw [q7, hf.readLE _ _ (Outside.of_sub hOut (by omega) (by omega)), tm5]
    · rw [q7, hf.readLE _ _ (Outside.of_sub hOut (by omega) (by omega)), tm6]
  have hpk : (Sc.regs 1).toNat = pS.toNat + k := by
    rw [r1]; exact add_toNat pS k (by simp only [Nat.reducePow]; omega)
  have hp2 : (Sc.regs 2).toNat = nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
    rw [r2]; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  have hb : ∀ j, j < (Sc.regs 2).toNat → Fv256.C.bytesAt Sc.mem (Sc.regs 1).toNat j =
      Fv256.C.bytesAt s.mem pS.toNat (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) := by
    intro j hj
    rw [hp2] at hj
    have hkq : k = startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := hk2 (by omega)
    rw [hpk, hkq]
    show Sc.mem.readLE (pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) 1 =
      s.mem.readLE (pS.toNat + (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1
    rw [Nat.add_assoc]
    exact topSt_byte hSt hpC _ (by omega)
  have hdp' := Fv256.TopMath.dec_of_fd (Fv256.C.bytesAt s.mem pS.toNat) (Fv256.C.bytesAt Sc.mem (Sc.regs 1).toNat)
    nS.toNat (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (Sc.regs 2).toNat hq hp2 hb hdp
  have hfr : ∀ rs rs2, MemFrame Sc.mem S1.mem rs → (∀ a n, Outside a n rs2 → Outside a n rs) →
      (∀ a n, Outside a n rs2 → Outside a n [(lo, hi)]) → MemFrame s.mem S2.mem rs2 := by
    intro rs rs2 hf h1 h2
    rw [q7]; exact MemFrame.trans tmf hf (fun a n h => ⟨h2 a n h, h1 a n h⟩)
  have hSc28 : Sc.regs 28 = s.regs 28 := t3
  have hSpV : S2.sp = s.sp := q1
  have hEnvS2 : ∀ rs, MemFrame Sc.mem S1.mem rs → (∀ a n, Outside a n [(lo, hi), (z.toNat, z.toNat + 32)] → Outside a n rs) →
      Env cfg R R2 T b L lo hi S2 := by
    intro rs hf h1
    refine Fv256.Arm64.SfdEnv.Env.frame hMod.1 tEnv ⟨by rw [hSpV]; omega, by rw [hSpV]; omega, by rw [hSpV]; omega⟩
      (q5.trans p28) (by rw [q7]; exact hf.mono h1) hzR hzP hzS (by rw [hSc28]; exact hzg)
  rcases hcases with ⟨hfd, e0, e1, e2, e3, hf⟩ | ⟨v, hfd, e0, e1, e2, e3, hf⟩ | ⟨lo', len', hfd, qq, tt, e0, e1, hte, hf⟩
  · -- eof
    obtain ⟨hpr1, hpr2, hpr3, hpr4, hpr5, hpr6⟩ := pre _ hf (by simp only [outside_cons, outside_nil, and_true]; omega)
    have hres : decParse (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = .eof := by rw [hdp', hfd]; rfl
    have hO1 : Outside cfg.ioEOF 8 [(lo, hi)] := by
      have := hEOFo; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
    have hO2 : Outside (cfg.ioEOF + 8) 8 [(lo, hi)] := by
      have := hEOFo; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
    refine ⟨hpr1, hpr2, hpr3, hpr4, hpr5, hpr6, Or.inr (Or.inl ⟨hres, ?_, ?_, ?_, ?_, ?_⟩)⟩
    · have e0' : (S1.regs 0).toNat = Sc.mem.readLE cfg.ioEOF 8 := e0
      rw [q3, e0', tmf.readLE _ _ hO1]
    · have e1' : (S1.regs 1).toNat = Sc.mem.readLE (cfg.ioEOF + 8) 8 := e1
      rw [q4, e1', tmf.readLE _ _ hO2]
    · rw [q7]; exact e2
    · exact hEnvS2 _ hf (fun a n h => outside_hi h (by omega))
    · exact hfr _ _ hf (fun a n h => outside_hi h (by omega))
        (fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; exact h.1)
  · -- ok
    obtain ⟨hpr1, hpr2, hpr3, hpr4, hpr5, hpr6⟩ := pre _ hf (by simp only [outside_cons, outside_nil, and_true]; omega)
    have hres : decParse (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = .ok v := by rw [hdp', hfd]; rfl
    refine ⟨hpr1, hpr2, hpr3, hpr4, hpr5, hpr6, Or.inl ⟨v, hres, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [q3]; exact e0
    · rw [q4]; exact e1
    · rw [q7]; exact e2
    · exact hEnvS2 _ hf (fun a n h => outside_hi h (by omega))
    · exact hfr _ _ hf (fun a n h => outside_hi h (by omega))
        (fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; exact h.1)
  · -- syntax
    have hres : decParse (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat =
        .syntax (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + lo') len' := by rw [hdp', hfd]; rfl
    obtain ⟨hs1, hs2, _⟩ := Fv256.I.Fv256.I.decParse_syntax _ _ _ _ hres
    have hkq : k = startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := hk2 (by omega)
    obtain ⟨hpr1, hpr2, hpr3, hpr4, hpr5, hpr6⟩ := pre _ hf (by
      simp only [outside_cons, outside_nil, outside_append, and_true]
      refine ⟨⟨Outside.of_sub e9 (by omega) (by omega), Outside.of_sub e10 (by omega) (by omega)⟩, by omega, by omega⟩)
    have hE8 : Outside cfg.strconvErrSyntax 8 [(lo, hi)] := by
      have := e14 (cfg.strconvErrSyntax, cfg.strconvErrSyntax + 16) (by simp [staticRanges])
      simp only [outside_cons, outside_nil, and_true, Nat.add_sub_cancel_left] at this ⊢; omega
    have hE8' : Outside (cfg.strconvErrSyntax + 8) 8 [(lo, hi)] := by
      have := e14 (cfg.strconvErrSyntax, cfg.strconvErrSyntax + 16) (by simp [staticRanges])
      simp only [outside_cons, outside_nil, and_true, Nat.add_sub_cancel_left] at this ⊢; omega
    refine ⟨hpr1, hpr2, hpr3, hpr4, hpr5, hpr6, Or.inr (Or.inr (Or.inr ⟨_, _, hres, qq, tt, ?_, ?_, ?_, ?_⟩))⟩
    · rw [q3]; exact e0
    · rw [q4]; exact e1
    · have hpp : pS.toNat + (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + lo') = (Sc.regs 1).toNat + lo' := by
        rw [hpk, hkq]; omega
      rw [hpp]
      obtain ⟨t1', t2', t3', t4', t5', t6', t7', t8', t9', t10', t11', t12'⟩ := hte
      refine ⟨t1', t2', t3', t4', by rw [q7]; exact t5', by rw [q7]; exact t6', by rw [q7]; exact t7',
        by rw [q7]; exact t8', ?_, ?_, ?_, ?_⟩
      · rw [q7, t9']; exact tmf.readLE _ _ hE8
      · rw [q7, t10']; exact tmf.readLE _ _ hE8'
      · intro kk hkk
        rw [q7, t11' kk hkk]
        refine tmf.readLE _ _ ?_
        simp only [outside_cons, outside_nil, and_true]
        simp only [BitVec.toNat_ofNat, Nat.reducePow] at hkk ⊢
        omega
      · rw [q7, ← hSc28]; exact t12'
    · refine hfr _ _ hf (fun a n h => ?_) (fun a n h => ?_)
      · simp only [outside_cons, outside_nil, outside_append, and_true] at h ⊢
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
        exact ⟨⟨h1, h2⟩, by omega, by omega⟩
      · simp only [outside_cons, outside_nil, outside_append, and_true] at h ⊢
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
        exact h3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- return `ErrBig256Range` (two words loaded from the package variable), pop the frame -/
theorem top_err (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S : State) (pcE : Nat) (hE : pcE = 0xb8a4c ∨ pcE = 0xb8a80) (hpc : S.pc = BitVec.ofNat 64 pcE)
    (hSt : TopSt R R2 T b L lo hi z pS s S) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (s.regs 30) S
      (fun S2 => S2.sp = s.sp ∧ S2.regs 29 = s.regs 29 ∧ S2.regs 28 = S.regs 28 ∧ S2.regs 18 = S.regs 18 ∧
        (S2.regs 0).toNat = S.mem.readLE cfg.errBig 8 ∧ (S2.regs 1).toNat = S.mem.readLE (cfg.errBig + 8) 8 ∧
        S2.mem = S.mem) := by
  obtain ⟨hl1, hl2, h0', h1', h2', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  obtain ⟨t1, t2, t3, t4, tmf, tm1, tm2, tm3, tm4, tm5, tm6, tEnv⟩ := hSt
  have hEnv0 := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv0
  have hspS : S.sp.toNat = s.sp.toNat - 80 := by
    rw [t1]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := s.sp.isLt; simp only [Nat.reducePow] at this; omega
  have hacc : S.mem.accessible (S.sp.toNat - 8) 16 false = true := by
    rw [tmf.accessible, hspS]
    exact Arm64.Memory.accessible_mono _ (Arm64.Memory.accessible_weaken _ e5) (by omega) (by omega)
  have hE16 : S.mem.accessible cfg.errBig 16 false = true := by rw [tmf.accessible]; exact hErrA
  have hx29 : S.mem.readLE (S.sp.toNat - 8) 8 = (s.regs 29).toNat := by
    rw [show S.sp.toNat - 8 = s.sp.toNat - 88 by omega]; exact tm2
  have hx30 : S.mem.readLE S.sp.toNat 8 = (s.regs 30).toNat := by
    rw [show S.sp.toNat = s.sp.toNat - 80 by omega]; exact tm1
  have hret : BitVec.ofNat 64 (S.mem.readLE S.sp.toNat 8) = s.regs 30 := by
    rw [hx30]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)
  have h29 : BitVec.ofNat 64 (S.mem.readLE (S.sp.toNat - 8) 8) = s.regs 29 := by
    rw [hx29]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)
  have hret' : BitVec.ofNat 64 (S.mem.readLE (s.sp.toNat - 80) 8) = s.regs 30 := by
    rw [tm1]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)
  have h29' : BitVec.ofNat 64 (S.mem.readLE (s.sp.toNat - 88) 8) = s.regs 29 := by
    rw [tm2]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)
  have hspV : S.sp + 80#64 = s.sp := by rw [t1]; bv_omega
  have hal : S.sp.toNat % 16 = 0 := by omega
  have hEB : cfg.errBig = 0x1b5b60 := rfl
  rcases hE with rfl | rfl
  · janus_run [hpc, hret, h29, hret', h29', hacc, hx29, hx30, hspV, hal, hl2, hl1, hE16, hEB]
  · janus_run [hpc, hret, h29, hret', h29', hacc, hx29, hx30, hspV, hal, hl2, hl1, hE16, hEB]

open Fv256.Arm64.SegCompose in
/-- `ErrBig256Range`: the documented result when the number is too large -/
theorem top_range (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S : State) (pcE : Nat) (hE : pcE = 0xb8a4c ∨ pcE = 0xb8a80) (hpc : S.pc = BitVec.ofNat 64 pcE)
    (hSt : TopSt R R2 T b L lo hi z pS s S)
    (hres : decParse (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = .range) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (s.regs 30) S (TopPost cfg R R2 T b L lo hi z pS nS s) := by
  have hpre' := hpre
  refine seg_mono (top_err impl R R2 T b L lo hi z pS nS s hpre S pcE hE hpc hSt) ?_
  intro S2 hS2
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hS2
  obtain ⟨hl1, hl2, h0', h1', h2', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  obtain ⟨t1, t2, t3, t4, tmf, tm1, tm2, tm3, tm4, tm5, tm6, tEnv⟩ := hSt
  have hO1 : Outside cfg.errBig 8 [(lo, hi)] := by
    have := hErrO; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
  have hO2 : Outside (cfg.errBig + 8) 8 [(lo, hi)] := by
    have := hErrO; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
  have hspS : S.sp.toNat = s.sp.toNat - 80 := by
    rw [t1]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := s.sp.isLt; simp only [Nat.reducePow] at this; omega
  have hEnv0 := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv0
  refine ⟨q1, q2, q3.trans t3, q4.trans t4, by rw [q7]; exact tm5, by rw [q7]; exact tm6,
    Or.inr (Or.inr (Or.inl ⟨hres, ?_, ?_, ?_, ?_, ?_⟩))⟩
  · rw [q5, tmf.readLE _ _ hO1]
  · rw [q6, tmf.readLE _ _ hO2]
  · unfold Janus.Spec.val256
    rw [q7, tmf.readLE _ _ (by have := hzlh; simp only [outside_cons, outside_nil, and_true]; omega)]
  · refine Fv256.Arm64.SfdEnv.Env.frame hMod.1 tEnv ⟨by rw [q1]; omega, by rw [q1]; omega, by rw [q1]; omega⟩ q3
      (by rw [q7]; exact MemFrame.refl _ _) hzR hzP hzS (by rw [t3]; exact hzg)
  · rw [q7]; exact tmf.mono (fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; exact h.1)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- more than 78 digits: the error exit -/
theorem top_c2 (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 0xb8a18) (hM : TopMid R R2 T b L lo hi z pS nS s S)
    (hgt : 78 < nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (BitVec.ofNat 64 0xb8a80) S
      (TopSt R R2 T b L lo hi z pS s) := by
  obtain ⟨hSt, h0, ⟨k, hk1, hk2, h1⟩, h2⟩ := hM
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpB, _⟩ := hpre
  have hmI := ofNat_toInt (nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (by omega)
  janus_run [hpc, h2, hmI] until [0xb8a80]
  all_goals exact hSt

theorem c3a_post (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S S' : State) (k : Nat) (hSt : TopSt R R2 T b L lo hi z pS s S)
    (hkq : k = startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)
    (heq : nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = 78)
    (hsp : S'.sp = S.sp) (h29 : S'.regs 29 = S.regs 29) (h28 : S'.regs 28 = S.regs 28) (h18 : S'.regs 18 = S.regs 18)
    (r0 : S'.regs 0 = pS + BitVec.ofNat 64 k) (r1 : S'.regs 1 = 78#64) (r2 : S'.regs 2 = BitVec.ofNat 64 cfg.maxStr)
    (r3 : S'.regs 3 = 78#64) (r30 : S'.regs 30 = BitVec.ofNat 64 0xb8a44)
    (hmem : S'.mem = (S.mem.writeLE (BitVec.toNat S.sp + 64) 8 (pS.toNat + k)).writeLE (BitVec.toNat S.sp + 56) 8 78) :
    Janus.Contracts.Cmpstring.CmpstringPre 16 S' ∧ CmpCtx R R2 T b L lo hi z pS nS s S' := by
  obtain ⟨hl1, hl2, h0', h1', h2', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  have hEnv0 := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv0
  have hnS := nS.isLt
  have hq := Fv256.TopMath.startPos_spec' (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hspS := topSt_sp hSt (by omega)
  have hmf : MemFrame S.mem S'.mem [(lo, hi)] := by
    rw [hmem]
    repeat' first
      | exact MemFrame.refl _ _
      | refine MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  have hSt' : TopSt R R2 T b L lo hi z pS s S' := by
    refine topSt_step hMod.1 hSt (by omega) hsp h29 h28 h18 hmf (by omega) ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (rw [hmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint])
  have hspS' : S'.sp.toNat = s.sp.toNat - 80 := by rw [hsp]; exact hspS
  have hpk : pS.toNat + k < 2 ^ 64 := by omega
  have hP := add_toNat pS k hpk
  refine ⟨⟨⟨by rw [r30]; decide, by rw [r30]; decide, by omega, by omega, by omega, by omega, ?_⟩, Or.inr ⟨?_, ?_⟩, Or.inr ⟨?_, ?_⟩⟩,
    hSt', r30, ?_, ?_, by rw [r0, hkq], r1, r2, r3, heq⟩
  · rw [hmf.accessible, topSt_acc hSt]; exact Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  · rw [r0, hP, r1, hmf.accessible, topSt_acc hSt]
    simp only [BitVec.toNat_ofNat, Nat.reducePow]
    exact Arm64.Memory.accessible_mono _ (hpA.resolve_left (by omega)) (by omega) (by omega)
  · rw [r0, hP, r1]; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  · rw [r2, r3, hmf.accessible, topSt_acc hSt]
    simp only [BitVec.toNat_ofNat, Nat.reducePow]
    exact hMaxA
  · rw [r2, r3]; simp only [BitVec.toNat_ofNat, Nat.reducePow]
    have : cfg.maxStr = 0xf490b := rfl
    omega
  · rw [hmem, hsp]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
  · rw [hmem, hsp]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl, hkq]; exact Nat.mod_eq_of_lt (by rw [← hkq]; omega)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- exactly 78 digits: spill and call `runtime.cmpstring` -/
theorem top_c3a (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 0xb8a18) (hM : TopMid R R2 T b L lo hi z pS nS s S)
    (heq : nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = 78) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (BitVec.ofNat 64 0x11cc0) S
      (fun S' => Janus.Contracts.Cmpstring.CmpstringPre 16 S' ∧ CmpCtx R R2 T b L lo hi z pS nS s S') := by
  have hpre' := hpre
  obtain ⟨hSt, h0, ⟨k, hk1, hk2, h1⟩, h2⟩ := hM
  obtain ⟨hl1, hl2, h0', h1', h2', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  have hEnv0 := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv0
  have hnS := nS.isLt
  have hq := Fv256.TopMath.startPos_spec' (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hspS := topSt_sp hSt (by omega)
  have hkq : k = startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := hk2 (by omega)
  have hmI := ofNat_toInt (nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (by omega)
  have hwacc : S.mem.accessible (S.sp.toNat + 56) 16 true = true := by
    rw [topSt_acc hSt]; exact Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  janus_run [hpc, h2, hmI, heq, hwacc] until [0x11cc0]
  all_goals (
    apply c3a_post R R2 T b L lo hi z pS nS s hpre' S _ k hSt hkq heq <;>
      first | rfl | simp [setReg_apply])

open Janus.Contracts.Cmpstring in
theorem cmp_after (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S' S'' : State) (hC : CmpCtx R R2 T b L lo hi z pS nS s S') (hpr : CmpstringPre 16 S')
    (hret : CmpRet 16 S' S'') :
    TopSt R R2 T b L lo hi z pS s S'' ∧ S''.pc = BitVec.ofNat 64 0xb8a44 ∧
      S''.regs 0 = BitVec.ofInt 64 (strCmp S'.mem (pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) cfg.maxStr 78 78) ∧
      S''.mem.readLE (S''.sp.toNat + 56) 8 = 78 ∧
      S''.mem.readLE (S''.sp.toNat + 64) 8 = pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧ S''.sp = S'.sp ∧
      S''.regs 28 = S'.regs 28 := by
  obtain ⟨hSt, r30, m56, m64, r0, r1, r2, r3, heq⟩ := hC
  obtain ⟨junk, f, v, m, hS, hf⟩ := hret
  obtain ⟨hl1, hl2, h0', h1', h2', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  have hspS := topSt_sp hSt (by omega)
  have hnS := nS.isLt
  have hq := Fv256.TopMath.startPos_spec' (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hf' : MemFrame S'.mem m [(lo, hi)] := by
    refine hf.mono (fun a n h => ?_)
    simp only [calleeStack, outside_cons, outside_nil, and_true] at h ⊢
    omega
  subst hS
  have hsp' : (retState S' junk [cmpResult S'] f v m).sp = S'.sp := rfl
  have hspS' : S'.sp.toNat = s.sp.toNat - 80 := hspS
  have hP0 : (S'.regs 0).toNat = pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
    rw [r0]; exact add_toNat pS _ (by omega)
  have hP1 : (S'.regs 1).toNat = 78 := by rw [r1]; rfl
  have hP2 : (S'.regs 2).toNat = cfg.maxStr := by
    rw [r2]; simp only [BitVec.toNat_ofNat, Nat.reducePow]
    have : cfg.maxStr = 0xf490b := rfl
    omega
  have hP3 : (S'.regs 3).toNat = 78 := by rw [r3]; rfl
  have hres : (retState S' junk [cmpResult S'] f v m).regs 0 =
      BitVec.ofInt 64 (strCmp S'.mem (pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) cfg.maxStr 78 78) := by
    simp only [retState, callRegs, cmpResult, List.getD_cons_zero]
    rw [hP0, hP1, hP2, hP3]
    simp
  have hOut : ∀ a n, (a + n ≤ S'.sp.toNat - 16 ∨ S'.sp.toNat - 8 ≤ a) → (a + n ≤ S'.sp.toNat + 8 ∨ S'.sp.toNat + 40 ≤ a) →
      Outside a n (calleeStack S' 16 4) := by
    intro a n h1 h2
    simp only [calleeStack, outside_cons, outside_nil, and_true]
    exact ⟨h1, h2⟩
  have hrd : ∀ a, (a + 8 ≤ S'.sp.toNat - 16 ∨ S'.sp.toNat - 8 ≤ a) → (a + 8 ≤ S'.sp.toNat + 8 ∨ S'.sp.toNat + 40 ≤ a) →
      m.readLE a 8 = S'.mem.readLE a 8 := fun a h1 h2 => hf.readLE a 8 (hOut a 8 h1 h2)
  refine ⟨?_, r30, hres, ?_, ?_, rfl, ?_⟩
  · refine topSt_step hMod.1 hSt (by omega) hsp' (by simp [retState, callRegs]) (by simp [retState, callRegs])
      (by simp [retState, callRegs]) hf' (by omega) ?_ ?_ ?_ ?_ ?_ ?_
    · exact hrd _ (by omega) (by omega)
    · exact hrd _ (by omega) (by omega)
    · exact hrd _ (by omega) (by omega)
    · exact hrd _ (by omega) (by omega)
    · exact hrd _ (by omega) (by omega)
    · exact hrd _ (by omega) (by omega)
  · show m.readLE (S'.sp.toNat + 56) 8 = 78
    rw [hrd _ (by omega) (by omega)]; exact m56
  · show m.readLE (S'.sp.toNat + 64) 8 = _
    rw [hrd _ (by omega) (by omega)]; exact m64
  · simp [retState, callRegs]

open Janus.Contracts.Cmpstring in
theorem cmp_val (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S' : State) (hSt : TopSt R R2 T b L lo hi z pS s S')
    (heq : nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = 78) :
    strCmp S'.mem (pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) cfg.maxStr 78 78 = 1 ↔
      lexGt (fun j => Fv256.C.bytesAt s.mem pS.toNat (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) maxDigit 78 := by
  obtain ⟨hl1, hl2, h0', h1', h2', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  have hq := Fv256.TopMath.startPos_spec' (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  rw [Fv256.I.strCmp_eq_one_iff S'.mem 78]
  refine Fv256.TopMath.lexGt_congr2 _ _ _ _ 78 (fun j hj => ?_) (fun j hj => ?_)
  · show S'.mem.readLE (pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) 1 =
      s.mem.readLE (pS.toNat + (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1
    rw [Nat.add_assoc]; exact topSt_byte hSt hpC _ (by omega)
  · rw [← hMaxB j hj]
    refine hSt.2.2.2.2.1.readLE _ _ ?_
    have := hMaxO
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega

open Fv256.Arm64.SegCompose in
set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- `cmpstring` says the 78 digits are above `2^256 - 1`: `ErrBig256Range` -/
theorem top_c3_gt (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S' S'' : State) (hC : CmpCtx R R2 T b L lo hi z pS nS s S') (hpr : Janus.Contracts.Cmpstring.CmpstringPre 16 S')
    (hret : Janus.Contracts.Cmpstring.CmpRet 16 S' S'')
    (hlex : lexGt (fun j => Fv256.C.bytesAt s.mem pS.toNat (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) maxDigit 78) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (s.regs 30) S'' (TopPost cfg R R2 T b L lo hi z pS nS s) := by
  have hpre' := hpre
  have heq := hC.2.2.2.2.2.2.2.2
  obtain ⟨hSt, hpc, hR0, m56, m64, hsp, h28⟩ := cmp_after R R2 T b L lo hi z pS nS s hpre S' S'' hC hpr hret
  have hv := (cmp_val R R2 T b L lo hi z pS nS s hpre S' hC.1 heq).2 hlex
  have hR0' : S''.regs 0 = 1#64 := by rw [hR0, hv]; rfl
  have h1 : ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (BitVec.ofNat 64 0xb8a4c) S''
      (TopSt R R2 T b L lo hi z pS s) := by
    obtain ⟨_, _, _, _, _, hMod, hEnv, hlo, hhi, _⟩ := hpre
    janus_run [hpc, hR0'] until [0xb8a4c]
    all_goals exact topSt_step hMod.1 hSt (by omega) hsp.symm rfl rfl rfl (MemFrame.refl _ _) (by have := hEnv.1; omega) rfl rfl rfl rfl rfl rfl
  refine seg_trans h1 (fun S3 hpc3 hSt3 => top_range impl R R2 T b L lo hi z pS nS s hpre' S3 0xb8a4c (Or.inl rfl) hpc3 hSt3 ?_)
  exact Fv256.TopMath.decParse_gt78 _ _ heq hlex

open Janus.Contracts.Cmpstring in
set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- `cmpstring` says the 78 digits are at most `2^256 - 1`: reload and call `fromDecimal` -/
theorem top_c3_le (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S' S'' : State) (hC : CmpCtx R R2 T b L lo hi z pS nS s S') (hpr : Janus.Contracts.Cmpstring.CmpstringPre 16 S')
    (hret : Janus.Contracts.Cmpstring.CmpRet 16 S' S'')
    (hlex : ¬ lexGt (fun j => Fv256.C.bytesAt s.mem pS.toNat (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) maxDigit 78) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (BitVec.ofNat 64 Fv256.Arm64.SfdFd.fd) S''
      (fun S3 => Fv256.Arm64.SfdFd.FdPre R R2 T b L lo (s.sp.toNat - 48) z (S3.regs 1) (S3.regs 2) S3 ∧
        FdCtx R R2 T b L lo hi z pS nS s 0xb8a74 S3) := by
  have hpre' := hpre
  have heq := hC.2.2.2.2.2.2.2.2
  obtain ⟨hSt, hpc, hR0, m56, m64, hsp, h28⟩ := cmp_after R R2 T b L lo hi z pS nS s hpre S' S'' hC hpr hret
  have hv := (cmp_val R R2 T b L lo hi z pS nS s hpre S' hC.1 heq)
  have hne : strCmp S'.mem (pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) cfg.maxStr 78 78 ≠ 1 :=
    fun h => hlex (hv.1 h)
  have hcases := Janus.Contracts.Cmpstring.strCmp_cases S'.mem (pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) cfg.maxStr 78 78
  have hcle : strCmp S'.mem (pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) cfg.maxStr 78 78 ≤ 0 := by omega
  obtain ⟨hl1, hl2, h0', h1', h2', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  have hEnv0 := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv0
  have hnS := nS.isLt
  have hq := Fv256.TopMath.startPos_spec' (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hspS := topSt_sp hSt (by omega)
  have hS'sp : S'.sp.toNat = s.sp.toNat - 80 := by rw [← hsp]; exact hspS
  have hR0v : S''.regs 0 = 0#64 ∨ S''.regs 0 = 18446744073709551615#64 := by
    rw [hR0]
    rcases hcases with h | h | h
    · right; rw [h]; decide
    · left; rw [h]; decide
    · exact absurd h hne
  have hz88 : S''.mem.readLE (S''.sp.toNat + 88) 8 = z.toNat := by
    have := hSt.2.2.2.2.2.2.2.1
    rw [show S''.sp.toNat + 88 = s.sp.toNat + 8 by omega]; exact this
  have hrd : S''.mem.accessible (S''.sp.toNat + 56) 40 false = true := by
    rw [topSt_acc hSt]; exact Arm64.Memory.accessible_mono _ (Arm64.Memory.accessible_weaken _ e5) (by omega) (by omega)
  have hpS := (BitVec.ofNat_toNat 64 pS.toNat).trans (BitVec.setWidth_eq _)
  have hz88' : S''.mem.readLE (S'.sp.toNat + 88) 8 = z.toNat := by rw [← hsp]; exact hz88
  have m56' : S''.mem.readLE (S'.sp.toNat + 56) 8 = 78 := by rw [← hsp]; exact m56
  have m64' : S''.mem.readLE (S'.sp.toNat + 64) 8 = pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
    rw [← hsp]; exact m64
  have hzz : BitVec.ofNat 64 z.toNat = z := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hfin : allDec (Fv256.C.bytesAt s.mem (pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)) 0 78 →
      decSum (Fv256.C.bytesAt s.mem (pS.toNat + startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)) 0 78 < 2 ^ 256 := by
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
    omega
  rcases hR0v with hv | hv <;>
  · janus_run [hpc, hv, hz88, m56, m64, hrd] until [0xb8b50]
    all_goals (
      refine ReachesRet.done (by first | rfl | decide) ?_
      refine call_post R R2 T b L lo hi z pS nS s hpre' S'' _ (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) 78 0xb8a74 hSt
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by decide) (by decide) (by omega) (Nat.le_refl _) hfin (Nat.le_refl _) (fun _ => rfl) heq.symm
      · exact hsp.symm
      · simp [setReg_apply]
      · simp [setReg_apply]
      · simp [setReg_apply]
      · rfl
      · simp [setReg_apply, hz88', hzz]
      · simp [setReg_apply, m64', BitVec.ofNat_add, hpS]
      · simp [setReg_apply, m56']
      · simp [setReg_apply])

end Fv256.Arm64.SfdTop
