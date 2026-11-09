import Fv256.Proofs.Amd64.SfdProg
import Fv256.Proofs.Common.SfdFdMath
import Fv256.Proofs.Common.SfdFdLem
import Fv256.Proofs.Common.UtilB2
import Fv256.Proofs.Amd64.SfdFd
import Fv256.Proofs.Amd64.SfdMul
import Fv256.Proofs.Common.SegCompose

/-!
# The chunk loop of `fromDecimal` (amd64): the loop-head invariant and the round bookkeeping
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd

namespace Fv256.Amd64.SfdFd

abbrev head : Nat := fd + 0xa0

/-- the state at the loop head after `i` rounds -/
def FdInv (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s0 : State) (i : Nat) (S : State) : Prop :=
  S.rip = BitVec.ofNat 64 head ∧ i ≤ 5 ∧
  S.regs 0 = z ∧ S.regs 3 = pS ∧ S.regs 2 = BitVec.ofNat 64 i ∧ S.regs 1 = nS - BitVec.ofNat 64 (19 * i) ∧
  (19 * i < nS.toNat → S.regs 6 = nS - BitVec.ofNat 64 (19 * i)) ∧
  S.regs 4 = s0.regs 4 - 144#64 ∧ S.regs 5 = s0.regs 4 - 8#64 ∧ S.regs 14 = s0.regs 14 ∧ S.xmm 15 = 0 ∧ S.df = false ∧
  S.fsBase = s0.fsBase ∧
  MemFrame s0.mem S.mem [(lo, hi), (z.toNat, z.toNat + 32)] ∧
  S.mem.readLE (s0.regs 4).toNat 8 = s0.mem.readLE (s0.regs 4).toNat 8 ∧
  S.mem.readLE ((s0.regs 4).toNat - 8) 8 = (s0.regs 5).toNat ∧
  S.mem.readLE ((s0.regs 4).toNat + 8) 8 = z.toNat ∧ S.mem.readLE ((s0.regs 4).toNat + 16) 8 = pS.toNat ∧
  (∀ k, k < 5 → S.mem.readLE ((s0.regs 4).toNat - 48 + 8 * k) 8 = s0.mem.readLE (mulTab + 8 * k) 8) ∧
  Janus.Spec.val256 S.mem z.toNat = accV (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat i ∧
  Env R R2 T b L lo hi S ∧
  firstBad (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat 0 5 0 = firstBad (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat 0 (5 - i) i ∧
  allDec (Fv256.C.bytesAt s0.mem pS.toNat) (nS.toNat - 19 * i) nS.toNat

theorem bv_sub_c (x : BitVec 64) (c : Nat) (hc2 : c < 2 ^ 64) (hc : c ≤ x.toNat) :
    (x - BitVec.ofNat 64 c).toNat = x.toNat - c := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  simp only [Nat.reducePow] at *
  omega

theorem bv_152_8 (a : BitVec 64) : a - 152#64 + 8#64 = a - 144#64 := by bv_omega

theorem ChunkOK.frame {R : RtInv} {R2 : IfaceModel} {L : List (Nat × Nat)} {b : Nat} {sp sl : BitVec 64} {lo hi : Nat}
    {m m' : Janus.Arm64.Memory} {ws : List (Nat × Nat)} (h : ChunkOK R R2 L b sp sl lo hi m) (hf : MemFrame m m' ws) :
    ChunkOK R R2 L b sp sl lo hi m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, by rw [hf.accessible]; exact h4, h5, h6, h7, h8⟩

theorem TeObj.congr_src {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {fp fl sp sl : BitVec 64} {s1 s0 s' : State} {q t : Nat}
    (h : TeObj R b L fp fl sp sl s1 s' q t) (hg : s1.regs 14 = s0.regs 14)
    (he : s1.mem.readLE strconvErrSyntax 8 = s0.mem.readLE strconvErrSyntax 8)
    (he2 : s1.mem.readLE (strconvErrSyntax + 8) 8 = s0.mem.readLE (strconvErrSyntax + 8) 8)
    (hb : ∀ k, k < sl.toNat → s1.mem.readLE (sp.toNat + k) 1 = s0.mem.readLE (sp.toNat + k) 1) :
    TeObj R b L fp fl sp sl s0 s' q t := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12⟩ := h
  refine ⟨o1, o2, o3, o4, o5, o6, o7, o8, ?_, ?_, ?_, ?_⟩
  · rw [o9, he]
  · rw [o10, he2]
  · intro k hk; rw [o11 k hk, hb k hk]
  · rw [← hg]; exact o12


theorem bv_ofNat_sub (x : BitVec 64) (c : Nat) (hc2 : c < 2 ^ 64) (hc : c ≤ x.toNat) :
    BitVec.ofNat 64 (x.toNat - c) = x - BitVec.ofNat 64 c := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  simp only [Nat.reducePow] at *
  omega

theorem bv_rem_next (x : BitVec 64) (i : Nat) (hi : 19 * i + 19 < 2 ^ 64) (hc : 19 * i + 19 ≤ x.toNat) :
    BitVec.ofNat 64 (x.toNat - 19 * i) - 19#64 = x - BitVec.ofNat 64 (19 * (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := x.isLt
  simp only [Nat.reducePow, BitVec.toNat_ofNat] at *
  omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem fd_next (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State)
    (hpre : FdPre R R2 T b L lo hi z pS nS s)
    (S : State) (i : Nat) (hI : FdInv R R2 T b L lo hi z pS nS s i S) (hi5 : i < 5) (hrem : 19 * i < nS.toNat)
    (S'' : State) (d : Nat)
    (hrip : S''.rip = BitVec.ofNat 64 head) (h0 : S''.regs 0 = z) (h3 : S''.regs 3 = pS)
    (h2 : S''.regs 2 = BitVec.ofNat 64 (i + 1)) (h1 : S''.regs 1 = nS - BitVec.ofNat 64 (19 * (i + 1)))
    (h6 : 19 * (i + 1) < nS.toNat → S''.regs 6 = nS - BitVec.ofNat 64 (19 * (i + 1)))
    (h4 : S''.regs 4 = s.regs 4 - 144#64) (h5 : S''.regs 5 = s.regs 4 - 8#64) (h14 : S''.regs 14 = s.regs 14)
    (hx15 : S''.xmm 15 = 0) (hdf : S''.df = false) (hfs : S''.fsBase = s.fsBase)
    (hFm : MemFrame S.mem S''.mem [((s.regs 4).toNat - 248, (s.regs 4).toNat - 48), (z.toNat, z.toNat + 32)])
    (hval : Janus.Spec.val256 S''.mem z.toNat = (accV (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat i + d * 10 ^ (19 * i)) % 2 ^ 256)
    (hdig : allDec (Fv256.C.bytesAt s.mem pS.toNat) (chunkBounds nS.toNat 0 i).1 (nS.toNat - 19 * i))
    (hd : d = decSum (Fv256.C.bytesAt s.mem pS.toNat) (chunkBounds nS.toNat 0 i).1
      (nS.toNat - 19 * i - (chunkBounds nS.toNat 0 i).1))
    (ihn : ∀ S', FdInv R R2 T b L lo hi z pS nS s (i + 1) S' →
      ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (retAddrOf s) S' (FdPost R R2 T b L lo hi z pS nS s)) :
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (retAddrOf s) S'' (FdPost R R2 T b L lo hi z pS nS s) := by
  obtain ⟨⟨hra1, hra2, hx15', hdf'⟩, h0', h3', h1', hn, hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA, hfin⟩ := hpre
  obtain ⟨hpc, hi5', r0, r3, r2, r1, r6, r4, r5, r14, rx15, rdf, rfs, hfr, mret, mbp, mz, mp, mtab, mval, hEnvS, hfb, hall⟩ := hI
  have hlo_i := chunk_lo_eq nS.toNat i
  have e4 : (s.regs 4).toNat % 8 = 0 := hEnv.2.2.2.1
  have hFm' : MemFrame S.mem S''.mem [(lo, hi), (z.toNat, z.toNat + 32)] := hFm.mono (by
    intro a n h
    simp only [outside_cons, outside_nil, and_true] at h ⊢
    omega)
  have hFs : MemFrame s.mem S''.mem [(lo, hi), (z.toNat, z.toNat + 32)] := hfr.trans hFm' (by
    intro a n h
    simp only [outside_cons, outside_nil, and_true] at h ⊢
    omega)
  have hall' : allDec (Fv256.C.bytesAt s.mem pS.toNat) (nS.toNat - 19 * (i + 1)) nS.toNat :=
    allDec_join (b := Fv256.C.bytesAt s.mem pS.toNat) (by rw [← hlo_i]; exact hdig) hall
  have hfin' : accV (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat (i + 1) < 2 ^ 256 :=
    accV_lt _ _ _ (by omega) (by omega) hall' hfin
  have hsucc := accV_succ (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat i hrem
  rw [← hlo_i] at hsucc
  have hacc1 : accV (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat (i + 1) =
      (accV (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat i + d * 10 ^ (19 * i)) % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt (by rw [hd]; omega), hd]
    omega
  refine ihn S'' ⟨hrip, by omega, h0, h3, h2, h1, h6, h4, h5, h14, hx15, hdf, hfs, hFs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hall'⟩
  · rw [hFm.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact mret
  · rw [hFm.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact mbp
  · rw [hFm.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact mz
  · rw [hFm.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact mp
  · intro k hk
    rw [hFm.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact mtab k hk
  · rw [hval, hacc1]
  · exact Env.frame hMod.1 hEnvS (by rw [h4, bv_sub_c _ 144 (by decide) (by omega)]; refine ⟨by omega, by omega, by omega⟩) (by rw [h14, r14]) hFm'
      hzR hzP hzS (by rw [r14]; exact hzg)
  · rw [hfb]; exact fb_good _ _ _ hi5 hrem (by rw [chunk_hi]; exact hdig)
end Fv256.Amd64.SfdFd
