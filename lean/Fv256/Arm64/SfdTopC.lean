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
  · rw [hpk, hlN, hf.accessible]; exact Arm64.Memory.accessible_mono _ hpA (by omega) (by omega)
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

end Fv256.Arm64.SfdTop
