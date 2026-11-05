import Fv256.Amd64.IntoBigDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Amd64.IntoBig

/-- The pc after the normalization loop of the in-place path: `cmp %rax,%rdx` (`IntoBig+0x166`). -/
abbrev pcFinF : Nat := Extracted.entry + 0x166

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- The in-place path (`cap(words) >= 4`) after the four words were stored and the length normalized. -/
theorem finF (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (z bp : BitVec 64) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret) (s : State)
    (hwb2 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hpre : Pre R b z bp s) (hz0 : z.toNat ≠ 0)
    (S : State) (hsp : S.regs 4 = s.regs 4 - 24#64) (h28 : S.regs 14 = s.regs 14) (h29 : S.regs 5 = s.regs 4 - 8#64)
    (hx15 : S.xmm 15 = s.xmm 15) (h_rd1 : S.mem.readLE (s.regs 4).toNat 8 = ret)
    (h_rd2 : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (A P len cap : Nat)
    (hfr : MemFrame s.mem S.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24), (bp.toNat, bp.toNat + 8),
      (A, A + 32)]))
    (hpc : S.rip = BitVec.ofNat 64 pcFinF) (h0 : S.regs 0 = BitVec.ofNat 64 len) (h1 : S.regs 1 = BitVec.ofNat 64 A)
    (h2 : S.regs 2 = BitVec.ofNat 64 cap) (h3 : S.regs 3 = bp)
    (hlen : len ≤ 4) (hcap : 4 ≤ cap) (hcap2 : cap < 2 ^ 63)
    (hPv : S.mem.readLE bp.toNat 8 = P) (hPs : s.mem.readLE bp.toNat 8 = P) (hAs : s.mem.readLE (P + 8) 8 = A)
    (hPa : s.mem.accessible P 32 true = true) (hP48 : P + 32 ≤ 2 ^ 48) (hPo : Outside P 32 R.rt)
    (hPd : Apart ((s.regs 4).toNat - 4128) 4152 P 32) (hPb : Apart bp.toNat 8 P 32) (hPz : Apart z.toNat 32 P 32)
    (hAa : s.mem.accessible A 32 true = true) (hA48 : A + 32 ≤ 2 ^ 48) (hAo : Outside A 32 R.rt)
    (hAd : Apart ((s.regs 4).toNat - 4128) 4152 A 32) (hAb : Apart bp.toNat 8 A 32) (hAz : Apart z.toNat 32 A 32)
    (hAP : Apart A 32 P 32)
    (hword : ∀ i, i < 4 → S.mem.readLE (A + 8 * i) 8 = s.mem.readLE (z.toNat + 8 * i) 8)
    (hnorm : len = 0 ∨ s.mem.readLE (z.toNat + 8 * (len - 1)) 8 ≠ 0)
    (hzero : ∀ i, len ≤ i → i < 4 → s.mem.readLE (z.toNat + 8 * i) 8 = 0)
    (hinv : R.inv b [] (s.regs 14).toNat (view R.rt [] S.mem)) (hP0 : P ≠ 0) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R z bp s s') := by
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hflag, hty1, hty2, hok1, hok2, hok3, hok4,
    hinv0, hbud, ⟨hbpa, hbpb⟩, hbpo, hbpd, hz⟩ := hpre
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset, Janus.Amd64.GoABI.stackguard0] at hg hb' ha hw hal hout hga hgr
  obtain ⟨hzp, hzo, hzd, hzb, hzP⟩ := hz hz0
  obtain ⟨hzpa, hzpb⟩ := hzp
  have hspn : (S.regs 4).toNat = (s.regs 4).toNat - 24 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  unfold Apart at hPd
  have hfacts : Hidden (Janus.Spec.Disjoint z.toNat 32 bp.toNat 8 ∧ Outside z.toNat 32 R.rt ∧ Apart bp.toNat 8 P 32 ∧
      Apart z.toNat 32 P 32 ∧ Apart ((s.regs 4).toNat - 4128) 4152 A 32 ∧ Apart bp.toNat 8 A 32 ∧
      Apart z.toNat 32 A 32 ∧ Apart A 32 P 32 ∧ Outside bp.toNat 8 R.rt ∧ Janus.Spec.Disjoint bp.toNat 8 ((s.regs 4).toNat - 4128) 4152 ∧
      (∀ i, i < 4 → S.mem.readLE (A + 8 * i) 8 = s.mem.readLE (z.toNat + 8 * i) 8) ∧
      (len = 0 ∨ s.mem.readLE (z.toNat + 8 * (len - 1)) 8 ≠ 0) ∧
      (∀ i, len ≤ i → i < 4 → s.mem.readLE (z.toNat + 8 * i) 8 = 0)) :=
    ⟨hzb, hzo, hPb, hPz, hAd, hAb, hAz, hAP, hbpo, hbpd, hword, hnorm, hzero⟩
  clear hzP hz hbpd hzd hzb hAd hAb hAz hAP hPb hPz hga hzo hword hnorm hzero hinv0 hbud hbpo
  have hret48 := hret.user
  janus64_data hd [hw]
  janus_eval_nat h_f : flagAddr
  rw [h_f] at hflag
  janus64_run calls [hwb2]
  all_goals (unfold Hidden at hfacts)
  all_goals (obtain ⟨hzb, hzo, hPb, hPz, hAd, hAb, hAz, hAP, hbpo, hbpd, hword, hnorm, hzero⟩ := hfacts)
  all_goals (have hPvC : ReadEq S.mem bp.toNat 8 P := hPv)
  all_goals (try simp only [hPv])
  all_goals (try simp only [hPs, hAs])
  all_goals (first
    | refine ⟨fun h => absurd h hz0, fun _ => ⟨P, ?_⟩, ?_, fun h0 => absurd (hPs.symm.trans h0) hP0⟩
    | refine ⟨hx15, fun h => absurd h hz0, fun _ => ⟨P, ?_⟩, ?_, fun h0 => absurd (hPs.symm.trans h0) hP0⟩)
  all_goals (try (refine bigout_of _ bp.toNat P A len cap _ (fun i => s.mem.readLE (z.toNat + 8 * i) 8) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (val256_bigAbs s.mem z.toNat)))
  all_goals (try simp only [hPv] at *)
  all_goals (try simp only [hPs, hAs])
  all_goals (try (refine frame_wb hfr ?_ ?_ ?_ ?_ <;> first | rfl | assumption | (constructor <;> omega)))
  all_goals (try janus_simp)
  all_goals first
    | (rw [read_wb ‹MemFrame _ _ _› ‹InRanges _ 16 _› hbpo (by unfold Janus.Spec.Disjoint at hbpd; omega),
         Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Janus.Spec.Disjoint at hbpd; omega),
         Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hPb; omega),
         Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hPb; omega)]
       first | done | exact hPvC)
    | exact hPvC
    | (intro i hi
       rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hAP; omega),
         Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hAP; omega),
         read_wb ‹MemFrame _ _ _› ‹InRanges _ 16 _› (Outside.of_sub hAo (by omega) (by omega)) (by unfold Apart at hAd; omega),
         Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hAd; omega),
         Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hAP; omega),
         Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hAP; omega)]
       exact hword i hi)
    | (intro i hi
       rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hAP; omega),
         Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hAP; omega),
         Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hAP; omega),
         Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hAP; omega)]
       exact hword i hi)
    | (with_reducible assumption)
    | omega
    | janus_live
    | janus_frame
    | (exact ⟨(P, P + 32), by simp, by omega, by omega⟩)
    | (exact ⟨(A, A + 32), by simp, by omega, by omega⟩)
    | (exact hfr.mono (fun a n hh => by
        simp only [outside_append, outside_cons, outside_nil, and_true] at hh ⊢
        exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.2⟩))
    | (unfold Apart at *; janus_clear_irrel2; omega)
    | (trace_state; fail "finF")
    | (refine frame_wb hfr ?_ ?_ ?_ ?_ <;> first | rfl | assumption | (constructor <;> omega); done)
    | (rw [read_wb ‹MemFrame _ _ _› ‹InRanges _ 16 _› hbpo (by unfold Janus.Spec.Disjoint at hbpd; omega)])

end Fv256.Amd64.IntoBig
