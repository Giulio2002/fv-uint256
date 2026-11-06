import Fv256.Amd64.SfdFdPro

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd

namespace Fv256.Amd64.SfdFd

/-- what the round head leaves behind besides `PwPre`: the spill slots (`RA` at `sp0-152`) and the preserved registers -/
def PwCtx (s S : State) (i : Nat) (nS : BitVec 64) (RA : Nat) (S1 : State) : Prop :=
  MemFrame S.mem S1.mem [((s.regs 4).toNat - 152, (s.regs 4).toNat - 48)] ∧
  S1.mem.readLE ((s.regs 4).toNat - 152) 8 = RA ∧ S1.mem.readLE ((s.regs 4).toNat - 104) 8 = i ∧
  S1.mem.readLE ((s.regs 4).toNat - 56) 8 = S.mem.readLE ((s.regs 4).toNat - 48 + 8 * i) 8 ∧
  S1.mem.readLE ((s.regs 4).toNat - 96) 8 = nS.toNat - 19 * i ∧ S1.mem.readLE ((s.regs 4).toNat - 112) 8 = nS.toNat - 19 * i ∧
  S1.regs 4 = s.regs 4 - 152#64 ∧ S1.regs 5 = s.regs 4 - 8#64 ∧ S1.regs 14 = s.regs 14 ∧ S1.xmm 15 = 0 ∧ S1.df = false ∧
  S1.fsBase = s.fsBase

theorem ChunkOK.mono_win {R : RtInv} {R2 : IfaceModel} {L : List (Nat × Nat)} {b : Nat} {sp sl : BitVec 64}
    {lo hi lo' hi' : Nat} {m m' : Janus.Arm64.Memory} {ws : List (Nat × Nat)}
    (h : ChunkOK R R2 L b sp sl lo hi m) (hf : MemFrame m m' ws) (h1 : lo ≤ lo') (h2 : hi' ≤ hi) :
    ChunkOK R R2 L b sp sl lo' hi' m' := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := h
  exact ⟨c1, c2, c3, by rw [hf.accessible]; exact c4, c5, by omega, c7, c8⟩

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- head of a round (big chunk) up to the call to `strconv.ParseUint` -/
theorem fd_to_pw (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State)
    (hpre : FdPre R R2 T b L lo hi z pS nS s)
    (S : State) (i : Nat) (hI : FdInv R R2 T b L lo hi z pS nS s i S) (hi5 : i < 5) (hrem : 19 * i < nS.toNat)
    (hbig : 19 < nS.toNat - 19 * i) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 pw) S
      (fun S1 => PwPre R R2 T b L ((s.regs 4).toNat - 4432) ((s.regs 4).toNat - 104)
        (BitVec.ofNat 64 (pS.toNat + (nS.toNat - 19 * (i + 1)))) 19#64 S1 ∧ PwCtx s S i nS 4933783 S1) := by
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0, h3, h1, hn78, hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA, hfin⟩ := hpre
  obtain ⟨hpc, hi5', r0, r3, r2, r1, r6, r4, r5, r14, rx15, rdf, rfs, hfr, mret, mbp, mz, mp, mtab, mval, hEnvS, hfb, hall⟩ := hI
  have hEnv' := hEnvS
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 144 := by rw [r4]; exact bv_sub_c _ 144 (by decide) (by omega)
  have hS1 : (S.regs 1).toNat = nS.toNat - 19 * i := by
    rw [r1]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := nS.isLt; simp only [Nat.reducePow] at *; omega
  have hS6 : (S.regs 6).toNat = nS.toNat - 19 * i := by
    rw [r6 hrem]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := nS.isLt; simp only [Nat.reducePow] at *; omega
  have hS2 : (S.regs 2).toNat = i := by rw [r2]; simp only [BitVec.toNat_ofNat]; omega
  have hgl : Amd64.load S.mem ((S.regs 14).toNat + 16) 8 = .ok (S.mem.readLE ((S.regs 14).toNat + 16) 8) := by
    simp [Amd64.load, e7]
  have hacc : S.mem.accessible ((S.regs 4).toNat - 8) 190 true = true :=
    Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  have hR2 : (S.regs 2).toInt = (i : Int) := by rw [BitVec.toInt_eq_toNat_cond, hS2]; split <;> omega
  janus64_run [hacc, hS4, hS1, hS6, hS2, hR2, r0, r1, r3, r2, r6, hrem, hbig] until [pw]
  all_goals trace_state
  all_goals sorry

end Fv256.Amd64.SfdFd
