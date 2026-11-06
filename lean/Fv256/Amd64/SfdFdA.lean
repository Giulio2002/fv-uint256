import Fv256.Amd64.SfdFdPost

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd

namespace Fv256.Amd64.SfdFd

abbrev m2 : Nat := fd + 0x1c4

/-- the merge point after the digits of round `i` were added into `z` (before the loop increment) -/
def M2Inv (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s0 : State) (i : Nat) (S : State) : Prop :=
  S.rip = BitVec.ofNat 64 m2 ∧ i < 5 ∧ 19 * i < nS.toNat ∧
  S.regs 6 = z ∧ S.regs 2 = BitVec.ofNat 64 i ∧ S.regs 8 = nS - BitVec.ofNat 64 (19 * i) ∧
  S.flags = (subFlags (nS - BitVec.ofNat 64 (19 * i)) 19#64 false).snd ∧
  S.regs 4 = s0.regs 4 - 144#64 ∧ S.regs 5 = s0.regs 4 - 8#64 ∧ S.regs 14 = s0.regs 14 ∧ S.xmm 15 = 0 ∧ S.df = false ∧
  S.fsBase = s0.fsBase ∧
  S.mem.readLE ((s0.regs 4).toNat - 96) 8 = nS.toNat - 19 * i ∧
  MemFrame s0.mem S.mem [(lo, hi), (z.toNat, z.toNat + 32)] ∧
  S.mem.readLE (s0.regs 4).toNat 8 = s0.mem.readLE (s0.regs 4).toNat 8 ∧
  S.mem.readLE ((s0.regs 4).toNat - 8) 8 = (s0.regs 5).toNat ∧
  S.mem.readLE ((s0.regs 4).toNat + 8) 8 = z.toNat ∧ S.mem.readLE ((s0.regs 4).toNat + 16) 8 = pS.toNat ∧
  (∀ k, k < 5 → S.mem.readLE ((s0.regs 4).toNat - 48 + 8 * k) 8 = s0.mem.readLE (mulTab + 8 * k) 8) ∧
  Janus.Spec.val256 S.mem z.toNat = accV (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat (i + 1) ∧
  Env R R2 T b L lo hi S ∧
  firstBad (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat 0 5 0 = firstBad (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat 0 (5 - (i + 1)) (i + 1) ∧
  allDec (Fv256.C.bytesAt s0.mem pS.toNat) (nS.toNat - 19 * (i + 1)) nS.toNat

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- round 0: `z := d` -/
theorem fd_mid0 (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State)
    (hn78 : nS.toNat ≤ 78) (hlo : lo + 4432 ≤ (s.regs 4).toNat) (hhi : (s.regs 4).toNat + 32 ≤ hi)
    (hzw : s.mem.accessible z.toNat 32 true = true) (hzb : z.toNat + 32 ≤ 2 ^ 48)
    (hzlh : z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat) (hzR : Outside z.toNat 32 R.rt ∨ InRanges z.toNat 32 L)
    (hzP : Outside z.toNat 32 R2.priv) (hzS : ∀ r ∈ staticRanges T, Outside r.1 (r.2 - r.1) [(z.toNat, z.toNat + 32)])
    (hzg : (s.regs 14).toNat + 16 + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 14).toNat + 16)
    (hMod : Mod R R2 T L) (hfin : allDec (Fv256.C.bytesAt s.mem pS.toNat) 0 nS.toNat → decSum (Fv256.C.bytesAt s.mem pS.toNat) 0 nS.toNat < 2 ^ 256)
    (S : State) (d : Nat) (hM : MidInv R R2 T b L lo hi z pS nS s 0 d S) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 m2) S (M2Inv R R2 T b L lo hi z pS nS s 0) := by
  obtain ⟨hpc, hi5, hrem, hd64, r0, r3, r1, r4, r5, r14, rx15, rdf, rfs, mi, mlen, mrem, mW, hfr, mret, mbp, mz, mp, mtab, mval, hEnv, hfb, hdig, hd, hall⟩ := hM
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 144 := by rw [r4]; exact bv_sub_c _ 144 (by decide) (by omega)
  have hacc : S.mem.accessible ((S.regs 4).toNat) 160 true = true :=
    Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  have hiS : S.mem.readLE ((S.regs 4).toNat + 40) 8 = 0 := by
    have : (S.regs 4).toNat + 40 = (s.regs 4).toNat - 104 := by omega
    rw [this]; exact mi
  have hzS' : S.mem.readLE ((S.regs 4).toNat + 152) 8 = z.toNat := by
    have : (S.regs 4).toNat + 152 = (s.regs 4).toNat + 8 := by omega
    rw [this]; exact mz
  have hlS : S.mem.readLE ((S.regs 4).toNat + 32) 8 = nS.toNat - 19 * 0 := by
    have : (S.regs 4).toNat + 32 = (s.regs 4).toNat - 112 := by omega
    rw [this]; exact mrem
  have hzacc : S.mem.accessible z.toNat 32 true = true := by rw [hfr.accessible]; exact hzw
  janus64_run [hacc, hzacc, hiS, hzS', hlS, hS4, r0, r1, Nat.mod_eq_of_lt (show z.toNat + 16 < 2 ^ 64 by omega)] until [m2]
  all_goals (
    refine reach_name ?_
    intro S2 hS2
    refine ReachesRet.done (by rw [hS2]; first | rfl | decide | simp [m2, fd]) ?_
    have hdv : d = accV (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat (0 + 1) := by
      have := accV_succ (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat 0 hrem
      rw [this, accV_zero]; rw [hd, chunk_lo_eq]; simp
    have hmf : MemFrame s.mem S2.mem [(lo, hi), (z.toNat, z.toNat + 32)] := by
      rw [hS2]; dsimp only
      repeat' first
        | exact hfr
        | refine MemFrame.writeLE ?_ _ (r := (z.toNat, z.toNat + 32)) (by simp) (by omega) (by omega)
    have hmfS : MemFrame S.mem S2.mem [(lo, hi), (z.toNat, z.toNat + 32)] := by
      rw [hS2]; dsimp only
      repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (r := (z.toNat, z.toNat + 32)) (by simp) (by omega) (by omega)
    have hg4 : S2.regs 4 = s.regs 4 - 144#64 := by simp [hS2, setRegF_apply, r4]
    have hg14 : S2.regs 14 = s.regs 14 := by simp [hS2, setRegF_apply, r14]
    have hspn : (S2.regs 4).toNat = (s.regs 4).toNat - 144 := by rw [hg4]; exact bv_sub_c _ 144 (by decide) (by omega)
    have hrdS : ∀ a, (a + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ a) → S2.mem.readLE a 8 = S.mem.readLE a 8 := by
      intro a ha; rw [hS2]; dsimp only
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    unfold M2Inv
    refine ⟨by rw [hS2]; first | rfl | decide | simp [m2, fd], hi5, hrem, ?a6, ?a2, ?a8, ?afl, hg4, ?a5, hg14, ?ax, ?adf, ?afs, ?mlen, hmf, ?mretM, ?mbpM,
      ?xz, ?xp, ?tab, ?val, ?env, ?fb, ?hall⟩
    case a6 => simp [hS2, setRegF_apply]
    case a2 => simp [hS2, setRegF_apply]
    case a8 => simp [hS2, setRegF_apply]
    case afl => simp [hS2]
    case a5 => simp [hS2, setRegF_apply, r5]
    case ax => rw [hS2]; simpa [setXmmF] using rx15
    case adf => simp [hS2, rdf]
    case afs => rw [hS2]; exact rfs
    case mlen => rw [hrdS _ (by omega)]; simpa using mlen
    case mretM => rw [hrdS _ (by omega)]; exact mret
    case mbpM => rw [hrdS _ (by omega)]; exact mbp
    case xz => rw [hrdS _ (by omega)]; exact mz
    case xp => rw [hrdS _ (by omega)]; exact mp
    case tab => intro k hk; rw [hrdS _ (by omega)]; exact mtab k hk
    case val =>
      rw [hS2]; dsimp only
      rw [z_store0 _ _ _ hd64, hdv]
    case env =>
      exact Env.frame hMod.1 hEnv (by rw [hspn]; refine ⟨by omega, by omega, by omega⟩) (by rw [hg14, r14]) hmfS hzR hzP hzS (by rw [r14]; exact hzg)
    case fb => rw [hfb]; exact fb_good _ _ _ hi5 hrem (by rw [chunk_hi]; exact hdig)
    case hall => have := hdig; rw [chunk_lo_eq] at this; simpa using this)

end Fv256.Amd64.SfdFd
