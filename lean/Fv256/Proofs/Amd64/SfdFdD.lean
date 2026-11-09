import Fv256.Proofs.Amd64.SfdFdC

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd

namespace Fv256.Amd64.SfdFd

theorem Env_of_eq {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {S S2 : State}
    (h : Env R R2 T b L lo hi S) (h4 : S2.regs 4 = S.regs 4) (h14 : S2.regs 14 = S.regs 14) (hm : S2.mem = S.mem) :
    Env R R2 T b L lo hi S2 := by
  unfold Env at *
  rw [h4, h14, hm]; exact h

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- the loop increment and the slice chop: back to the head with `i + 1` -/
theorem fd_incr (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (i : Nat) (S : State)
    (hn78 : nS.toNat ≤ 78) (hlo : lo + 4432 ≤ (s.regs 4).toNat) (hhi : (s.regs 4).toNat + 32 ≤ hi)
    (hM : M2Inv R R2 T b L lo hi z pS nS s i S) :
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (BitVec.ofNat 64 head) S (FdInv R R2 T b L lo hi z pS nS s (i + 1)) := by
  obtain ⟨hpc, hi5, hrem, r6, r2, r8, hfl, r4, r5, r14, rx15, rdf, rfs, mlen, hfr, mret, mbp, mz, mp, mtab, mval, hEnv, hfb, hall⟩ := hM
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 144 := by rw [r4]; exact bv_sub_c _ 144 (by decide) (by omega)
  have hacc : S.mem.accessible ((S.regs 4).toNat) 160 true = true :=
    Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  have hlen : S.mem.readLE ((S.regs 4).toNat + 48) 8 = nS.toNat - 19 * i := by
    have : (S.regs 4).toNat + 48 = (s.regs 4).toNat - 96 := by omega
    rw [this]; exact mlen
  have hpSs : S.mem.readLE ((S.regs 4).toNat + 160) 8 = pS.toNat := by
    have : (S.regs 4).toNat + 160 = (s.regs 4).toNat + 16 := by omega
    rw [this]; exact mp
  have hsub : (nS - BitVec.ofNat 64 (19 * i)).toNat = nS.toNat - 19 * i := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := nS.isLt; simp only [Nat.reducePow] at *; omega
  by_cases hb : 19 < nS.toNat - 19 * i
  · janus64_run [hacc, hS4, hlen, hpSs, hfl, r6, r2, r8, hsub] until [head]
    all_goals (
      refine reach_name ?_
      intro S2 hS2
      refine ReachesRet.done (by rw [hS2]; first | rfl | decide | simp [head, fd]) ?_
      have hm2 : S2.mem = S.mem := by rw [hS2]
      have h42 : S2.regs 4 = S.regs 4 := by simp [hS2, setRegF_apply]
      have h142 : S2.regs 14 = S.regs 14 := by simp [hS2, setRegF_apply]
      unfold FdInv
      refine ⟨by rw [hS2]; first | rfl | simp [head, fd], by omega, ?a0, ?a3, ?a2, ?a1, ?a6, by rw [h42, r4], by simp [hS2, setRegF_apply, r5], by rw [h142, r14],
        by rw [hS2]; exact rx15, by simp [hS2, rdf], by rw [hS2]; try exact rfs, by rw [hm2]; exact hfr, by rw [hm2]; exact mret,
        by rw [hm2]; exact mbp, by rw [hm2]; exact mz, by rw [hm2]; exact mp, by rw [hm2]; exact mtab, by rw [hm2]; exact mval,
        Env_of_eq hEnv h42 h142 hm2, hfb, hall⟩
      case a0 => simp [hS2, setRegF_apply]
      case a3 => simp [hS2, setRegF_apply]
      case a2 => simp [hS2, setRegF_apply]
      case a1 => simp [hS2, setRegF_apply, Nat.mul_add]
      case a6 =>
        intro h
        first
        | (exfalso; omega)
        | simp [hS2, setRegF_apply, Nat.mul_add])
  · janus64_run [hacc, hS4, hlen, hpSs, hfl, r6, r2, r8, hsub] until [head]
    all_goals (
      refine reach_name ?_
      intro S2 hS2
      refine ReachesRet.done (by rw [hS2]; first | rfl | decide | simp [head, fd]) ?_
      have hm2 : S2.mem = S.mem := by rw [hS2]
      have h42 : S2.regs 4 = S.regs 4 := by simp [hS2, setRegF_apply]
      have h142 : S2.regs 14 = S.regs 14 := by simp [hS2, setRegF_apply]
      unfold FdInv
      refine ⟨by rw [hS2]; first | rfl | simp [head, fd], by omega, ?a0, ?a3, ?a2, ?a1, ?a6, by rw [h42, r4], by simp [hS2, setRegF_apply, r5], by rw [h142, r14],
        by rw [hS2]; exact rx15, by simp [hS2, rdf], by rw [hS2]; try exact rfs, by rw [hm2]; exact hfr, by rw [hm2]; exact mret,
        by rw [hm2]; exact mbp, by rw [hm2]; exact mz, by rw [hm2]; exact mp, by rw [hm2]; exact mtab, by rw [hm2]; exact mval,
        Env_of_eq hEnv h42 h142 hm2, hfb, hall⟩
      case a0 => simp [hS2, setRegF_apply]
      case a3 => simp [hS2, setRegF_apply]
      case a2 => simp [hS2, setRegF_apply]
      case a1 => simp [hS2, setRegF_apply, Nat.mul_add]
      case a6 =>
        intro h
        first
        | (exfalso; omega)
        | simp [hS2, setRegF_apply, Nat.mul_add])

end Fv256.Amd64.SfdFd
