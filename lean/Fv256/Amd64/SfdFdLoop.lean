import Extracted
import Fv256.SfdFdMath
import Fv256.SfdFdLem
import Fv256.UtilB2
import Fv256.Amd64.SfdFd
import Fv256.Amd64.SfdMul

/-!
# The chunk loop of `fromDecimal` (amd64): one round
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
      ReachesRet (Extracted.program.link impl) (retAddrOf s) S' (FdPost R R2 T b L lo hi z pS nS s)) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S'' (FdPost R R2 T b L lo hi z pS nS s) := by
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

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
theorem fd_round (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State)
    (hif : Ifaceeq (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hpre : FdPre R R2 T b L lo hi z pS nS s)
    (S : State) (i : Nat) (hI : FdInv R R2 T b L lo hi z pS nS s i S) (hi5 : i < 5) (hrem : 19 * i < nS.toNat)
    (S1 : State) (W V RA : Nat) (hrip : S1.rip = BitVec.ofNat 64 pw)
    (hr0 : S1.regs 0 = BitVec.ofNat 64 (pS.toNat + (chunkBounds nS.toNat 0 i).1))
    (hr3 : S1.regs 3 = BitVec.ofNat 64 (nS.toNat - 19 * i - (chunkBounds nS.toNat 0 i).1))
    (hr1 : S1.regs 1 = 10#64) (hr7 : S1.regs 7 = 64#64) (hr4 : S1.regs 4 = s.regs 4 - 152#64) (hr5 : S1.regs 5 = s.regs 4 - 8#64)
    (hr14 : S1.regs 14 = s.regs 14)
    (hrx : S1.xmm 15 = 0) (hrdf : S1.df = false) (hrfs : S1.fsBase = s.fsBase)
    (hm : S1.mem = ((((S.mem.writeLE ((s.regs 4).toNat - 104) 8 i).writeLE ((s.regs 4).toNat - 56) 8 W).writeLE
      ((s.regs 4).toNat - 96) 8 V).writeLE ((s.regs 4).toNat - 112) 8 V).writeLE ((s.regs 4).toNat - 152) 8 RA)
    (hV : V % 2 ^ 64 = nS.toNat - 19 * i) (hW : W = S.mem.readLE ((s.regs 4).toNat - 48 + 8 * i) 8)
    (hRA : RA = 4933783 ∨ RA = 4933806)
    (ihn : ∀ S', FdInv R R2 T b L lo hi z pS nS s (i + 1) S' →
      ReachesRet (Extracted.program.link impl) (retAddrOf s) S' (FdPost R R2 T b L lo hi z pS nS s)) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S1 (FdPost R R2 T b L lo hi z pS nS s) := by
  have hpreC := hpre
  have hIC := hI
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0, h3, h1, hn, hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA, hfin⟩ := hpre
  obtain ⟨hpc, hi5', r0, r3, r2, r1, r6, r4, r5, r14, rx15, rdf, rfs, hfr, mret, mbp, mz, mp, mtab, mval, hEnvS, hfb, hall⟩ := hI
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 144 := by rw [r4]; exact bv_sub_c _ 144 (by decide) (by omega)
  have hS1_4 : (S1.regs 4).toNat = (s.regs 4).toNat - 152 := by rw [hr4]; exact bv_sub_c _ 152 (by decide) (by omega)
  have hlo_i := chunk_lo_eq nS.toNat i
  have hlen1 : 1 ≤ nS.toNat - 19 * i - (chunkBounds nS.toNat 0 i).1 := by omega
  have hlen2 : nS.toNat - 19 * i - (chunkBounds nS.toNat 0 i).1 ≤ 19 := by omega
  have hrsp8 : (s.regs 4).toNat % 8 = 0 := e4
  have hF1 : MemFrame S.mem S1.mem [((s.regs 4).toNat - 152, (s.regs 4).toNat - 48)] := by
    rw [hm]
    refine ((((MemFrame.refl S.mem _).writeLE _ (r := ((s.regs 4).toNat - 152, (s.regs 4).toNat - 48)) (by simp)
      (by dsimp only; omega) (by dsimp only; omega)).writeLE _ (r := ((s.regs 4).toNat - 152, (s.regs 4).toNat - 48)) (by simp)
      (by dsimp only; omega) (by dsimp only; omega)).writeLE _ (r := ((s.regs 4).toNat - 152, (s.regs 4).toNat - 48)) (by simp)
      (by dsimp only; omega) (by dsimp only; omega)).writeLE _ (r := ((s.regs 4).toNat - 152, (s.regs 4).toNat - 48)) (by simp)
      (by dsimp only; omega) (by dsimp only; omega) |>.writeLE _ (r := ((s.regs 4).toNat - 152, (s.regs 4).toNat - 48)) (by simp)
      (by dsimp only; omega) (by dsimp only; omega)
  have hF1' : MemFrame S.mem S1.mem [(lo, hi)] := hF1.mono (by
    intro a n h
    simp only [outside_cons, outside_nil, and_true] at h ⊢
    omega)
  have hfr1 : MemFrame s.mem S1.mem [(lo, hi), (z.toNat, z.toNat + 32)] := hfr.trans hF1 (by
    intro a n h
    simp only [outside_cons, outside_nil, and_true] at h ⊢
    omega)
  have hg1 : S1.regs 14 = S.regs 14 := by rw [hr14, r14]
  have hEnv1 : Env R R2 T b L lo hi S1 :=
    Env.frame0 hMod.1 hEnvS (by rw [hS1_4]; refine ⟨by omega, by omega, by omega⟩) hg1 hF1' (by omega)
  have hpP : (BitVec.ofNat 64 (pS.toNat + (chunkBounds nS.toNat 0 i).1)).toNat = pS.toNat + (chunkBounds nS.toNat 0 i).1 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := pS.isLt; omega)
  have hlL : (BitVec.ofNat 64 (nS.toNat - 19 * i - (chunkBounds nS.toNat 0 i).1)).toNat = nS.toNat - 19 * i - (chunkBounds nS.toNat 0 i).1 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hCK := hCA (pS.toNat + (chunkBounds nS.toNat 0 i).1) (nS.toNat - 19 * i - (chunkBounds nS.toNat 0 i).1)
    (by omega) (by omega) hlen1 hlen2
  have hCK1 := ChunkOK.frame hCK hfr1
  have hRAlt : RA < 2 ^ 64 := by rcases hRA with h | h <;> subst h <;> decide
  have hret1 : S1.mem.readLE (S1.regs 4).toNat 8 = RA := by
    rw [hS1_4, hm]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
    have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    rw [h8]; exact Nat.mod_eq_of_lt hRAlt
  have hS1acc : ∀ a n w, S1.mem.accessible a n w = s.mem.accessible a n w := hfr1.accessible
  refine ReachesRet.call (pw_sum impl R R2 T b L lo hi _ _ hif hnew hmg hmv hwb1 hwb2) hrip
    ⟨⟨?_, ?_, ?_, ?_⟩, hr0, hr3, hr1, hr7, ?_, ?_, hMod, hEnv1, ?_, ?_, hCK1⟩ ?cont
  · rw [hS1acc, hS1_4]; exact Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ e5 (by omega) (by omega))
  · rw [hret1]; omega
  · exact hrx
  · exact hrdf
  · omega
  · omega
  · omega
  · omega
  case cont =>
    intro s' hpc' ⟨⟨k1, k2, k3, k4, k5, k6, k7⟩, hcase⟩
    have hra : retAddrOf S1 = BitVec.ofNat 64 RA := by simp only [retAddrOf, hret1]
    rw [hra] at k1
    have kk4 : s'.regs 4 = s.regs 4 - 144#64 := by rw [k2, hr4]; exact bv_152_8 _
    have kk5 : s'.regs 5 = s.regs 4 - 8#64 := by rw [k3, hr5]
    have kk14 : s'.regs 14 = s.regs 14 := by rw [k4, hr14]
    have kk15 : s'.xmm 15 = 0 := by rw [k5]; exact hrx
    have kkdf : s'.df = false := by rw [k6]; exact hrdf
    rw [hS1_4] at *
    rcases hRA with hRA | hRA
    all_goals
      subst hRA
      rcases hcase with ⟨hA, hv, hz3, hz1, hE', hfrOk⟩ | ⟨hA, hz0, ⟨q, t, hz3, hz1, hobj⟩, hfrE⟩
      · have hFS : MemFrame S.mem s'.mem [((s.regs 4).toNat - 248, (s.regs 4).toNat - 48)] := hF1.trans hfrOk (by
          intro a n h
          simp only [outside_cons, outside_nil, and_true] at h ⊢
          omega)
        have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
        have hq1 : s'.mem.readLE ((s.regs 4).toNat - 104) 8 = i := by
          rw [hfrOk.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), hm]
          simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
          rw [h8]; exact Nat.mod_eq_of_lt (by omega)
        have hq2 : s'.mem.readLE ((s.regs 4).toNat - 56) 8 = W := by
          rw [hfrOk.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), hm]
          simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
          rw [h8]; exact Nat.mod_eq_of_lt (by have := Janus.Arm64.Memory.readLE_lt S.mem ((s.regs 4).toNat - 48 + 8 * i) 8; rw [← hW] at this; simpa [h8] using this)
        have hq3 : s'.mem.readLE ((s.regs 4).toNat - 112) 8 = nS.toNat - 19 * i := by
          rw [hfrOk.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), hm]
          simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
          rw [h8, hV]
        have hq4 : s'.mem.readLE ((s.regs 4).toNat - 96) 8 = nS.toNat - 19 * i := by
          rw [hfrOk.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), hm]
          simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
          rw [h8, hV]
        have hq5 : s'.mem.readLE ((s.regs 4).toNat + 8) 8 = z.toNat := by
          rw [hFS.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact mz
        have hq6 : s'.mem.readLE ((s.regs 4).toNat + 16) 8 = pS.toNat := by
          rw [hFS.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact mp
        have hz3b : s'.regs 3 = 0 := hz3
        have hbyt : ∀ k, k < nS.toNat - 19 * i - (chunkBounds nS.toNat 0 i).1 →
            Fv256.C.bytesAt S1.mem (pS.toNat + (chunkBounds nS.toNat 0 i).1) k =
            Fv256.C.bytesAt s.mem pS.toNat ((chunkBounds nS.toNat 0 i).1 + k) := by
          intro k hk
          unfold Fv256.C.bytesAt
          rw [hfr1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
          rw [Nat.add_assoc]
        rw [hpP, hlL] at hA hv
        have hA' := (chunk_allDec_iff (Fv256.C.bytesAt s.mem pS.toNat) (Fv256.C.bytesAt S1.mem (pS.toNat + (chunkBounds nS.toNat 0 i).1))
          (chunkBounds nS.toNat 0 i).1 (nS.toNat - 19 * i - (chunkBounds nS.toNat 0 i).1) hbyt).1 hA
        have hdv : (s'.regs 0).toNat = decSum (Fv256.C.bytesAt s.mem pS.toNat) (chunkBounds nS.toNat 0 i).1
            (nS.toNat - 19 * i - (chunkBounds nS.toNat 0 i).1) := by
          rw [hv]; exact chunk_decSum _ _ _ _ hbyt
        have hdig : allDec (Fv256.C.bytesAt s.mem pS.toNat) (chunkBounds nS.toNat 0 i).1 (nS.toNat - 19 * i) := by
          have e : (chunkBounds nS.toNat 0 i).1 + (nS.toNat - 19 * i - (chunkBounds nS.toNat 0 i).1) = nS.toNat - 19 * i := by omega
          rw [e] at hA'; exact hA'
        have hFS2 : MemFrame S.mem s'.mem [((s.regs 4).toNat - 248, (s.regs 4).toNat - 48), (z.toNat, z.toNat + 32)] :=
          hFS.mono (by
            intro a n h
            simp only [outside_cons, outside_nil, and_true] at h ⊢
            omega)
        have hs4' : (s'.regs 4).toNat = (s.regs 4).toNat - 144 := by rw [kk4]; exact bv_sub_c _ 144 (by decide) (by omega)
        have hacS : s'.mem.accessible lo (hi - lo) false = true := by
          rw [hFS2.accessible lo (hi - lo) false, hfr.accessible lo (hi - lo) false]; exact Arm64.Memory.accessible_weaken _ e5
        by_cases hi0 : i = 0
        · subst hi0
          janus64_run [kk4, kk5, kk14, kk15, kkdf, hz3b, hq1, hq2, hq3, hq4, hq5, hq6, hs4', hacS] until [head]
          all_goals
            refine reach_name ?_
            intro S2 hS2
            refine fd_next impl R R2 T b L lo hi z pS nS s hpreC S 0 hIC hi5 hrem S2 (s'.regs 0).toNat ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hdig hdv ihn
            · subst hS2; rfl
            · subst hS2; simp [setRegF_apply]
            · subst hS2; simp [setRegF_apply]
            · subst hS2; simp [setRegF_apply]
            · subst hS2; simp [setRegF_apply]
            · intro h
              first
              | (exfalso; omega)
              | (subst hS2; simp [setRegF_apply])
            · subst hS2; simp [setRegF_apply, kk4]
            · subst hS2; simp [setRegF_apply, kk5]
            · subst hS2; simp [setRegF_apply, kk14]
            · subst hS2; simp [setRegF_apply, kk15]
            · subst hS2; simp [setRegF_apply, kkdf]
            · subst hS2; simp [setRegF_apply, k7, hrfs]
            · subst hS2
              exact ((hFS2.writeLE _ (r := (z.toNat, z.toNat + 32)) (by simp) (by dsimp only; omega) (by dsimp only; omega)).writeLE _
                (r := (z.toNat, z.toNat + 32)) (by simp) (by dsimp only; omega) (by dsimp only; omega)).writeLE _
                (r := (z.toNat, z.toNat + 32)) (by simp) (by dsimp only; omega) (by dsimp only; omega)
            · subst hS2
              show Janus.Spec.val256 (((s'.mem.writeLE (z.toNat + 16) 16 0).writeLE (z.toNat + 8) 8 0).writeLE z.toNat 8 (s'.regs 0).toNat) z.toNat = _
              rw [z_store0 _ _ _ (s'.regs 0).isLt, accV_zero]
              have := (s'.regs 0).isLt
              simp only [Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
              exact (Nat.mod_eq_of_lt (by omega)).symm
        · obtain ⟨hMa, hMb, hMv, hMo⟩ := hMult.2.2 i (by omega) (by omega)
          have hWeq : W = s.mem.readLE (mulTab + 8 * i) 8 := by rw [hW]; exact mtab i hi5
          rw [← hWeq] at hMa hMb hMv hMo
          simp only [outside_cons, outside_nil, and_true] at hMo
          have hWm : W % 2 ^ 64 = W := Nat.mod_eq_of_lt (by omega)
          have hMo' : W + 32 ≤ lo ∨ hi ≤ W := hMo.1
          janus64_run [kk4, kk5, kk14, kk15, kkdf, hz3b, hq1, hq2, hq3, hq4, hq5, hq6, hs4', hacS, hWm, hMb, hMa, hMo'] until [Fv256.Amd64.SfdMul.mulEntry]
          refine reach_name ?_
          intro S3 hS3
          have hS3m : S3.mem = (((s'.mem.writeLE ((s.regs 4).toNat - 88) 16 0).writeLE ((s.regs 4).toNat - 72) 16 0).writeLE
              ((s.regs 4).toNat - 88) 8 (s'.regs 0).toNat).writeLE ((s.regs 4).toNat - 152) 8 4933898 := by subst hS3; rfl
          have hrs : (S3.regs 4).toNat = (s.regs 4).toNat - 152 := by
            have : S3.regs 4 = s.regs 4 - 152#64 := by subst hS3; simp [setRegF_apply, kk4]
            rw [this]; exact bv_sub_c _ 152 (by decide) (by omega)
          have hbase : (s.regs 4 - 88#64).toNat = (s.regs 4).toNat - 88 := bv_sub_c _ 88 (by decide) (by omega)
          have hS3F : MemFrame s'.mem S3.mem [((s.regs 4).toNat - 152, (s.regs 4).toNat - 144), ((s.regs 4).toNat - 88, (s.regs 4).toNat - 56)] := by
            rw [hS3m]
            exact ((((MemFrame.refl s'.mem _).writeLE _ (r := ((s.regs 4).toNat - 88, (s.regs 4).toNat - 56)) (by simp)
              (by dsimp only; omega) (by dsimp only; omega)).writeLE _ (r := ((s.regs 4).toNat - 88, (s.regs 4).toNat - 56)) (by simp)
              (by dsimp only; omega) (by dsimp only; omega)).writeLE _ (r := ((s.regs 4).toNat - 88, (s.regs 4).toNat - 56)) (by simp)
              (by dsimp only; omega) (by dsimp only; omega)).writeLE _ (r := ((s.regs 4).toNat - 152, (s.regs 4).toNat - 144)) (by simp)
              (by dsimp only; omega) (by dsimp only; omega)
          have hS3acc : ∀ a n w, S3.mem.accessible a n w = s.mem.accessible a n w := by
            intro a n w; rw [hS3F.accessible, hFS2.accessible, hfr.accessible]
          have hS3ret : S3.mem.readLE (s.regs 4).toNat 8 = 0 ∨ True := Or.inr trivial
          have hS3r : S3.mem.readLE ((s.regs 4).toNat - 152) 8 = 4933898 := by
            rw [hS3m]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
          have hS3reg4' : S3.regs 4 = s.regs 4 - 152#64 := by subst hS3; simp [setRegF_apply, kk4]
          have hS3g : S3.regs 14 = s.regs 14 := by subst hS3; simp [setRegF_apply, kk14]
          have hr0 : S3.regs 0 = s.regs 4 - 88#64 := by subst hS3; simp [setRegF_apply]
          have hr3 : S3.regs 3 = s.regs 4 - 88#64 := by subst hS3; simp [setRegF_apply]
          have hr1 : S3.regs 1 = BitVec.ofNat 64 W := by subst hS3; simp [setRegF_apply]
          have hx3 : S3.xmm 15 = 0 := by subst hS3; simpa using kk15
          have hdf3 : S3.df = false := by subst hS3; simpa using kkdf
          refine ReachesRet.call (Fv256.B.summary_link impl (Fv256.Amd64.SfdMul.mul_sum (s.regs 4 - 88#64) (s.regs 4 - 88#64)
            (BitVec.ofNat 64 W))) (by subst hS3; rfl) ?pre ?cont
          case pre =>
            refine ⟨⟨?_, ?_, hx3, hdf3⟩, hr0, hr3, hr1, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
            all_goals try simp only [regSP, hrs, hbase, hS3acc, hS3r, Nat.reduceMul]
            all_goals first
              | omega
              | decide
              | (exact Arm64.Memory.accessible_mono _ e5 (by omega) (by omega))
              | (exact Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)))
              | (simp only [BitVec.toNat_ofNat, hWm]; first | omega | exact hMa)
          case cont =>
            intro S4 hpc4 hpost
            obtain ⟨⟨k1, k2, k3, k4, k5, k6, k7⟩, m0, mv, mfr⟩ := hpost
            simp only [regSP] at mfr
            have hdlt : (s'.regs 0).toNat < 2 ^ 64 := (s'.regs 0).isLt
            have hA3 : valueAt S3 (s.regs 4 - 88#64) 32 = (s'.regs 0).toNat := by
              unfold valueAt
              rw [hbase, hS3m]
              exact z_store3 _ _ _ _ _ _ (by omega) hdlt (by omega)
            have hB3 : valueAt S3 (BitVec.ofNat 64 W) 32 = 10 ^ (19 * i) := by
              unfold valueAt
              rw [BitVec.toNat_ofNat, hWm]
              rw [hS3F.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
                hFS.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
                hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
              exact hMv
            rw [hA3, hB3] at mv
            have hFo : ∀ a n, Outside a n [((s.regs 4).toNat - 168, (s.regs 4).toNat - 144), ((s.regs 4).toNat - 88, (s.regs 4).toNat - 56)] →
                S4.mem.readLE a n = s'.mem.readLE a n := by
              intro a n h
              rw [mfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega),
                hS3F.readLE _ _ (by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)]
            have hz4 : S4.mem.readLE z.toNat 32 = accV (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat i := by
              rw [hFo _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
                hFS.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
              exact mval
            have hp4 : S4.mem.readLE ((s.regs 4).toNat - 88) 32 = (s'.regs 0).toNat * 10 ^ (19 * i) % 2 ^ 256 := by
              have := mv
              unfold valueAt Fv256.Spec.mul at this
              rw [hbase] at this
              simpa [Fv256.Spec.W] using this
            have hx5 : S4.mem.readLE ((s.regs 4).toNat + 8) 8 = z.toNat := by
              rw [hFo _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hq5
            have hx1 : S4.mem.readLE ((s.regs 4).toNat - 104) 8 = i := by
              rw [hFo _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hq1
            have hy3 : S4.mem.readLE ((s.regs 4).toNat - 112) 8 = nS.toNat - 19 * i := by
              rw [hFo _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hq3
            have hx4 : S4.mem.readLE ((s.regs 4).toNat - 96) 8 = nS.toNat - 19 * i := by
              rw [hFo _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hq4
            have hx6 : S4.mem.readLE ((s.regs 4).toNat + 16) 8 = pS.toNat := by
              rw [hFo _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hq6
            have hS4reg4 : S4.regs 4 = s'.regs 4 := by rw [k2, hS3reg4', kk4]; exact bv_152_8 _
            have hS4acc : S4.mem.accessible lo (hi - lo) false = true := by
              rw [mfr.accessible, hS3F.accessible, hFS.accessible, hfr.accessible]; exact Arm64.Memory.accessible_weaken _ e5
            have hz4a : S4.mem.accessible z.toNat 32 true = true := by
              rw [mfr.accessible, hS3F.accessible, hFS.accessible, hfr.accessible]; exact hz
            have hs4n : (S4.regs 4).toNat = (s.regs 4).toNat - 144 := by rw [hS4reg4]; exact hs4'
            have hs4g : S4.regs 14 = s.regs 14 := by rw [k4, hS3g]
            have hs4x : S4.xmm 15 = 0 := by rw [k5]; exact hx3
            have hs4d : S4.df = false := by rw [k6]; exact hdf3
            rw [Fv256.Util.readLE_32] at hz4 hp4
            janus64_run [hS4reg4, hs4n, hs4g, hs4x, hs4d, hz4, hp4, hx5, hx1, hy3, hx4, hx6, hz4a, hS4acc] until [fd + 0x1ab]
            janus64_run [hS4reg4, hs4n, hs4g, hs4x, hs4d, hy3, hx4, hx6, hS4acc] until [fd + 0x1c4]
            have hFa : MemFrame S.mem S3.mem [((s.regs 4).toNat - 248, (s.regs 4).toNat - 48), (z.toNat, z.toNat + 32)] :=
              hFS2.trans hS3F (by
                intro a n h
                simp only [outside_cons, outside_nil, and_true] at h ⊢
                omega)
            have hFb : MemFrame S.mem S4.mem [((s.regs 4).toNat - 248, (s.regs 4).toNat - 48), (z.toNat, z.toNat + 32)] :=
              hFa.trans mfr (by
                intro a n h
                simp only [outside_cons, outside_nil, and_true] at h ⊢
                omega)
            have hlim : ∀ (M : Janus.Arm64.Memory) a, M.readLE a 8 < 2 ^ 64 := fun M a => by
              simpa using Janus.Arm64.Memory.readLE_lt M a 8
            have hXs : Janus.Spec.val256 S.mem z.toNat = S.mem.readLE z.toNat 8 + 2 ^ 64 * S.mem.readLE (z.toNat + 8) 8 +
                2 ^ 128 * S.mem.readLE (z.toNat + 16) 8 + 2 ^ 192 * S.mem.readLE (z.toNat + 24) 8 := by
              unfold Janus.Spec.val256; exact Fv256.Util.readLE_32 _ _
            have hYs : (s'.regs 0).toNat * 10 ^ (19 * i) % 2 ^ 256 = S4.mem.readLE ((s.regs 4).toNat - 88) 8 +
                2 ^ 64 * S4.mem.readLE ((s.regs 4).toNat - 80) 8 + 2 ^ 128 * S4.mem.readLE ((s.regs 4).toNat - 72) 8 +
                2 ^ 192 * S4.mem.readLE ((s.regs 4).toNat - 64) 8 := by
              have e1 : (s.regs 4).toNat - 88 + 8 = (s.regs 4).toNat - 80 := by omega
              have e2 : (s.regs 4).toNat - 88 + 16 = (s.regs 4).toNat - 72 := by omega
              have e3 : (s.regs 4).toNat - 88 + 24 = (s.regs 4).toNat - 64 := by omega
              rw [e1, e2, e3] at hp4; exact hp4.symm
            janus64_run [hS4reg4, hs4n, hs4g, hs4x, hs4d, hy3, hx4, hx6, hS4acc] until [fd + 0x1da, fd + 0x1c6]
            all_goals janus64_run [hS4reg4, hs4n, hs4g, hs4x, hs4d, hy3, hx4, hx6, hS4acc] until [head]
            all_goals trace_state
            all_goals sorry
      · have hz3c : s'.regs 3 = 5184000#64 := by rw [hz3]; rfl
        janus64_run [hz3c] until [fd + 0x1e5]
        trace_state
        sorry

end Fv256.Amd64.SfdFd
