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

theorem name_state {P : State → Prop} {S0 : State} (h : ∀ S1, S1 = S0 → P S1) : P S0 := h S0 rfl

theorem bv_chunk_p2 (nS pS : BitVec 64) (i : Nat) (hn : nS.toNat ≤ 78) (hi : 19 * i + 19 ≤ nS.toNat)
    (hp : pS.toNat + nS.toNat ≤ 2 ^ 48) :
    nS - BitVec.ofNat 64 (19 * i) + pS - 19#64 = BitVec.ofNat 64 (pS.toNat + (nS.toNat - 19 * (i + 1))) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := nS.isLt; have := pS.isLt
  simp only [Nat.reducePow] at *
  omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- head of a round (big chunk) up to the call to `strconv.ParseUint` -/
theorem fd_to_pw (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State)
    (hpre : FdPre R R2 T b L lo hi z pS nS s)
    (S : State) (i : Nat) (hI : FdInv R R2 T b L lo hi z pS nS s i S) (hi5 : i < 5) (hrem : 19 * i < nS.toNat)
    (hbig : 19 < nS.toNat - 19 * i) :
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (BitVec.ofNat 64 pw) S
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
  have hacc : S.mem.accessible ((S.regs 4).toNat - 8) 144 true = true :=
    Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  have hR2 : (S.regs 2).toInt = (i : Int) := by rw [BitVec.toInt_eq_toNat_cond, hS2]; split <;> omega
  have hRi : (BitVec.ofNat 64 i).toInt = (i : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]; split <;> omega
  have hR1 : (S.regs 1).toInt = ((nS.toNat - 19 * i : Nat) : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, hS1]; split <;> omega
  have hsub : (nS - BitVec.ofNat 64 (19 * i)).toNat = nS.toNat - 19 * i := by rw [← r1]; exact hS1
  have hsf : (nS - BitVec.ofNat 64 (19 * i)).msb = false := by
    rw [BitVec.msb_eq_decide, hsub]; simp; omega
  have hzf : (18446744073709551616 - 19 * i + nS.toNat) % 18446744073709551616 ≠ 0 := by omega
  janus64_run [hacc, hS4, hS1, hS6, hS2, hR2, hRi, hR1, hsf, hzf, r0, r1, r3, r2, r6, hrem, hbig] until [pw]
  all_goals (
    refine name_state (P := fun S1 => PwPre R R2 T b L ((s.regs 4).toNat - 4432) ((s.regs 4).toNat - 104)
        (BitVec.ofNat 64 (pS.toNat + (nS.toNat - 19 * (i + 1)))) 19#64 S1 ∧ PwCtx s S i nS 4933783 S1) ?_
    intro S1 hS1
    have hm : S1.mem = ((((S.mem.writeLE ((s.regs 4).toNat - 104) 8 i).writeLE ((s.regs 4).toNat - 56) 8
        (S.mem.readLE ((s.regs 4).toNat - 144 + i * 8 + 96) 8)).writeLE ((s.regs 4).toNat - 96) 8
        (18446744073709551616 - 19 * i + nS.toNat)).writeLE ((s.regs 4).toNat - 112) 8
        (18446744073709551616 - 19 * i + nS.toNat)).writeLE ((s.regs 4).toNat - 152) 8 4933783 := by rw [hS1]
    have ea : (s.regs 4).toNat - 144 + i * 8 + 96 = (s.regs 4).toNat - 48 + 8 * i := by omega
    rw [ea] at hm
    have hg4 : S1.regs 4 = s.regs 4 - 152#64 := by simp [hS1, setRegF_apply]
    have hs1 : (S1.regs 4).toNat = (s.regs 4).toNat - 152 := by rw [hg4]; exact bv_sub_c _ 152 (by decide) (by omega)
    have hg14 : S1.regs 14 = s.regs 14 := by simp [hS1, setRegF_apply, r14]
    have hmf : MemFrame S.mem S1.mem [((s.regs 4).toNat - 152, (s.regs 4).toNat - 48)] := by
      rw [hm]
      repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (r := ((s.regs 4).toNat - 152, (s.regs 4).toNat - 48)) (by simp) (by omega) (by omega)
    have hmf1 : MemFrame S.mem S1.mem [(lo, hi)] := hmf.mono (by
      intro a n h
      simp only [outside_cons, outside_nil, and_true] at h ⊢
      omega)
    have hmf3 : MemFrame S.mem S1.mem [(lo, hi), (z.toNat, z.toNat + 32)] := hmf.mono (by
      intro a n h
      simp only [outside_cons, outside_nil, and_true] at h ⊢
      omega)
    have hmf2 : MemFrame s.mem S1.mem [(lo, hi), (z.toNat, z.toNat + 32)] := hfr.trans hmf3 (by
      intro a n h
      simp only [outside_cons, outside_nil, and_true] at h ⊢
      omega)
    have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    have hx15' : S1.xmm 15 = 0 := by simp [hS1]; exact rx15
    have hdf' : S1.df = false := by simp [hS1, rdf]
    have hret : S1.mem.readLE ((s.regs 4).toNat - 152) 8 = 4933783 := by
      rw [hm]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
      all_goals (try (rw [h8]; exact Nat.mod_eq_of_lt (by decide)))
    refine ⟨?pre, ?ctx⟩
    case ctx =>
      refine ⟨hmf, hret, ?_, ?_, ?_, ?_, hg4, ?_, hg14, hx15', hdf', ?_⟩
      · rw [hm]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [h8]; exact Nat.mod_eq_of_lt (by omega)
      · rw [hm]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [h8]; exact Nat.mod_eq_of_lt (Util.readLE8_lt _ _)
      · rw [hm]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [h8]; have := nS.isLt; simp only [Nat.reducePow] at this; omega
      · rw [hm]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [h8]; have := nS.isLt; simp only [Nat.reducePow] at this; omega
      · simp [hS1, setRegF_apply, r5]
      · simp [hS1, rfs]
    case pre =>
      have hn19 : (19#64 : BitVec 64).toNat = 19 := rfl
      refine ⟨⟨?_, ?_, hx15', hdf'⟩, ?_, ?_, ?_, ?_, ?_, ?_, hMod, ?env, ?lo, ?hi, ?chunk⟩
      · rw [hmf.accessible, hs1]
        exact Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ e5 (by omega) (by omega))
      · rw [hs1, hret]; decide
      · simp [hS1, setRegF_apply]; exact bv_chunk_p2 nS pS i hn78 (by omega) hpw
      · simp [hS1, setRegF_apply]
      · simp [hS1, setRegF_apply]
      · simp [hS1, setRegF_apply]
      · rw [hn19]; omega
      · rw [hn19]; omega
      case env =>
        refine Env.shrink (lo := lo) (hi := hi) (Env.frame0 hMod.1 hEnvS ?_ (by rw [hg14, r14]) hmf1 (by omega)) (by omega) (by omega) ?_ ?_
        · rw [hs1]; refine ⟨by omega, by omega, by omega⟩
        · rw [hs1]; omega
        · rw [hs1]; omega
      case lo => rw [hs1]; omega
      case hi => rw [hs1]; omega
      case chunk =>
        have hc := hCA (pS.toNat + (nS.toNat - 19 * (i + 1))) 19 (by omega) (by omega) (by omega) (by omega)
        exact ChunkOK.mono_win hc hmf2 (by omega) (by omega))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- head of a round (last chunk, at most 19 digits) up to the call to `strconv.ParseUint` -/
theorem fd_to_pw_small (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State)
    (hpre : FdPre R R2 T b L lo hi z pS nS s)
    (S : State) (i : Nat) (hI : FdInv R R2 T b L lo hi z pS nS s i S) (hi5 : i < 5) (hrem : 19 * i < nS.toNat)
    (hsmall : nS.toNat - 19 * i ≤ 19) :
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (BitVec.ofNat 64 pw) S
      (fun S1 => PwPre R R2 T b L ((s.regs 4).toNat - 4432) ((s.regs 4).toNat - 104)
        pS (nS - BitVec.ofNat 64 (19 * i)) S1 ∧ PwCtx s S i nS 4933806 S1) := by
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
  have hacc : S.mem.accessible ((S.regs 4).toNat - 8) 144 true = true :=
    Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  have hR2 : (S.regs 2).toInt = (i : Int) := by rw [BitVec.toInt_eq_toNat_cond, hS2]; split <;> omega
  have hRi : (BitVec.ofNat 64 i).toInt = (i : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]; split <;> omega
  have hR1 : (S.regs 1).toInt = ((nS.toNat - 19 * i : Nat) : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, hS1]; split <;> omega
  have hsub : (nS - BitVec.ofNat 64 (19 * i)).toNat = nS.toNat - 19 * i := by rw [← r1]; exact hS1
  have hsf : (nS - BitVec.ofNat 64 (19 * i)).msb = false := by
    rw [BitVec.msb_eq_decide, hsub]; simp; omega
  have hzf : (18446744073709551616 - 19 * i + nS.toNat) % 18446744073709551616 ≠ 0 := by omega
  have hsub : (nS - BitVec.ofNat 64 (19 * i)).toNat = nS.toNat - 19 * i := by rw [← r1]; exact hS1
  have hsf : (nS - BitVec.ofNat 64 (19 * i)).msb = false := by
    rw [BitVec.msb_eq_decide, hsub]; simp; omega
  have hzf : (18446744073709551616 - 19 * i + nS.toNat) % 18446744073709551616 ≠ 0 := by omega
  janus64_run [hacc, hS4, hS1, hS6, hS2, hR2, hRi, hR1, hsf, hzf, r0, r1, r3, r2, r6, hrem] until [pw]
  all_goals (
    refine name_state (P := fun S1 => PwPre R R2 T b L ((s.regs 4).toNat - 4432) ((s.regs 4).toNat - 104)
        pS (nS - BitVec.ofNat 64 (19 * i)) S1 ∧ PwCtx s S i nS 4933806 S1) ?_
    intro S1 hS1
    have hm : S1.mem = ((((S.mem.writeLE ((s.regs 4).toNat - 104) 8 i).writeLE ((s.regs 4).toNat - 56) 8
        (S.mem.readLE ((s.regs 4).toNat - 144 + i * 8 + 96) 8)).writeLE ((s.regs 4).toNat - 96) 8
        (18446744073709551616 - 19 * i + nS.toNat)).writeLE ((s.regs 4).toNat - 112) 8
        (18446744073709551616 - 19 * i + nS.toNat)).writeLE ((s.regs 4).toNat - 152) 8 4933806 := by rw [hS1]
    have ea : (s.regs 4).toNat - 144 + i * 8 + 96 = (s.regs 4).toNat - 48 + 8 * i := by omega
    rw [ea] at hm
    have hg4 : S1.regs 4 = s.regs 4 - 152#64 := by simp [hS1, setRegF_apply]
    have hs1 : (S1.regs 4).toNat = (s.regs 4).toNat - 152 := by rw [hg4]; exact bv_sub_c _ 152 (by decide) (by omega)
    have hg14 : S1.regs 14 = s.regs 14 := by simp [hS1, setRegF_apply, r14]
    have hmf : MemFrame S.mem S1.mem [((s.regs 4).toNat - 152, (s.regs 4).toNat - 48)] := by
      rw [hm]
      repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (r := ((s.regs 4).toNat - 152, (s.regs 4).toNat - 48)) (by simp) (by omega) (by omega)
    have hmf1 : MemFrame S.mem S1.mem [(lo, hi)] := hmf.mono (by
      intro a n h
      simp only [outside_cons, outside_nil, and_true] at h ⊢
      omega)
    have hmf3 : MemFrame S.mem S1.mem [(lo, hi), (z.toNat, z.toNat + 32)] := hmf.mono (by
      intro a n h
      simp only [outside_cons, outside_nil, and_true] at h ⊢
      omega)
    have hmf2 : MemFrame s.mem S1.mem [(lo, hi), (z.toNat, z.toNat + 32)] := hfr.trans hmf3 (by
      intro a n h
      simp only [outside_cons, outside_nil, and_true] at h ⊢
      omega)
    have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    have hx15' : S1.xmm 15 = 0 := by simp [hS1]; exact rx15
    have hdf' : S1.df = false := by simp [hS1, rdf]
    have hret : S1.mem.readLE ((s.regs 4).toNat - 152) 8 = 4933806 := by
      rw [hm]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
      all_goals (try (rw [h8]; exact Nat.mod_eq_of_lt (by decide)))
    refine ⟨?pre, ?ctx⟩
    case ctx =>
      refine ⟨hmf, hret, ?_, ?_, ?_, ?_, hg4, ?_, hg14, hx15', hdf', ?_⟩
      · rw [hm]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [h8]; exact Nat.mod_eq_of_lt (by omega)
      · rw [hm]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [h8]; exact Nat.mod_eq_of_lt (Util.readLE8_lt _ _)
      · rw [hm]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [h8]; have := nS.isLt; simp only [Nat.reducePow] at this; omega
      · rw [hm]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [h8]; have := nS.isLt; simp only [Nat.reducePow] at this; omega
      · simp [hS1, setRegF_apply, r5]
      · simp [hS1, rfs]
    case pre =>
      have hn19 : (19#64 : BitVec 64).toNat = 19 := rfl
      refine ⟨⟨?_, ?_, hx15', hdf'⟩, ?_, ?_, ?_, ?_, ?_, ?_, hMod, ?env, ?lo, ?hi, ?chunk⟩
      · rw [hmf.accessible, hs1]
        exact Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ e5 (by omega) (by omega))
      · rw [hs1, hret]; decide
      · simp [hS1, setRegF_apply, r3]
      · simp [hS1, setRegF_apply, r6 hrem]
      · simp [hS1, setRegF_apply]
      · simp [hS1, setRegF_apply]
      · rw [hsub]; omega
      · rw [hsub]; omega
      case env =>
        refine Env.shrink (lo := lo) (hi := hi) (Env.frame0 hMod.1 hEnvS ?_ (by rw [hg14, r14]) hmf1 (by omega)) (by omega) (by omega) ?_ ?_
        · rw [hs1]; refine ⟨by omega, by omega, by omega⟩
        · rw [hs1]; omega
        · rw [hs1]; omega
      case lo => rw [hs1]; omega
      case hi => rw [hs1]; omega
      case chunk =>
        have hc := hCA pS.toNat (nS.toNat - 19 * i) (by omega) (by omega) (by omega) (by omega)
        have hpe : BitVec.ofNat 64 pS.toNat = pS := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
        have hle : nS - BitVec.ofNat 64 (19 * i) = BitVec.ofNat 64 (nS.toNat - 19 * i) := by
          apply BitVec.eq_of_toNat_eq; rw [hsub, BitVec.toNat_ofNat]; have := nS.isLt; exact (Nat.mod_eq_of_lt (by omega)).symm
        rw [hpe, ← hle] at hc
        exact ChunkOK.mono_win hc hmf2 (by omega) (by omega))

end Fv256.Amd64.SfdFd
