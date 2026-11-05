import Fv256.Arm64.IntoBigFinF

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.IntoBig

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- `IntoBig` after `*b` is known to hold a (non-nil) `big.Int` pointer `P`. -/
theorem mid (impl : List Segment) (R : RtInv) (b : Nat) (z bp : BitVec 64) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret) (s : State)
    (hnew : NewobjectLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb2 : WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hpre : Pre R b z bp s) (hz0 : z.toNat ≠ 0)
    (S : State) (hrel : Rel R ret z bp s S) (hpc : S.pc = BitVec.ofNat 64 pcLoad)
    (h0 : S.regs 0 = z) (h1 : S.regs 1 = bp)
    (P : Nat) (h_rdP : S.mem.readLE bp.toNat 8 = P)
    (hcase : (s.mem.readLE bp.toNat 8 = P ∧ P ≠ 0 ∧ R.inv b [] (s.regs 28).toNat (view R.rt [] S.mem)) ∨
      (s.mem.readLE bp.toNat 8 = 0 ∧ InRanges P 32 R.rt ∧ ZeroBytes S.mem P 32 ∧
        Apart (s.sp.toNat - 4144) 4168 P 32 ∧ Apart bp.toNat 8 P 32 ∧
        S.mem.accessible P 32 true = true ∧ P + 32 ≤ 2 ^ 48 ∧
        R.inv (b - 32) [(P, P + 32)] (s.regs 28).toNat (view R.rt [(P, P + 32)] S.mem))) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R z bp s s') := by
  have hpre0 := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hflag, hty1, hty2, hok1, hok2, hok3, hok4,
    hinv0, hbud, ⟨hbpa, hbpb⟩, hbpo, hbpd, hz⟩ := hpre
  obtain ⟨hsp, h28, h29, h18, h_rd1, h_rd2, h_rd3, h_rd4, hfr⟩ := hrel
  obtain ⟨hzp, hzo, hzd, hzb, hzP⟩ := hz hz0
  simp only [Disjoint] at hbpd hzd hzb
  have hblk := Janus.Contracts.AllocSat.le_blockSize 32 false
  have hblk2 := Janus.Contracts.AllocSat.le_blockSize 32 true
  have hspn : S.sp.toNat = s.sp.toNat - 48 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  janus_data hd [hw]
  janus_eval_nat h_b : bigType
  janus_eval_nat h_a : arrType
  janus_eval_nat h_f : flagAddr
  rw [h_b] at hty1 hok1
  rw [h_a] at hty2 hok2
  rw [h_f] at hflag
  obtain ⟨hzpa, hzpb⟩ := hzp
  rcases hcase with ⟨hP, hP0, hinvS⟩ | ⟨hP0, hIn, hZ, hAs, hAb, hAcc, hP48, hinvS⟩
  · have hPlt : P < 2 ^ 64 := by
      rw [← hP]; simpa using Janus.Arm64.Memory.readLE_lt s.mem bp.toNat 8
    obtain ⟨hPp, hPo, hPd, hPb, hPz, hPA⟩ := hzP (by omega)
    rw [hP] at hPp hPo hPd hPb hPz hPA
    obtain ⟨hPpa, hPpb⟩ := ptr_of hPlt hPp
    simp only [Disjoint] at hPd hPb hPz
    by_cases hcap : 4 ≤ s.mem.readLE (P + 24) 8 ∧ s.mem.readLE (P + 24) 8 < 2 ^ 63
    · obtain ⟨hAp, hAo, hAd, hAb', hAz, hAP⟩ := hPA hcap.1
      have hAlt : s.mem.readLE (P + 8) 8 < 2 ^ 64 := by simpa using Janus.Arm64.Memory.readLE_lt s.mem (P + 8) 8
      obtain ⟨hApa, hApb⟩ := ptr_of hAlt hAp
      simp only [Disjoint] at hAd hAb' hAz hAP
      have hcapS : 4 ≤ S.mem.readLE (P + 24) 8 := by
        rw [hfr.readLE (P + 24) 8 (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨Outside.of_sub hPo (by omega) (by omega), by omega, by omega⟩)]
        exact hcap.1
      have hcapLt : s.mem.readLE (P + 24) 8 < 2 ^ 64 := by simpa using Janus.Arm64.Memory.readLE_lt s.mem (P + 24) 8
      janus_run until [Extracted.entry + 0x74, Extracted.entry + 0xa0]
      janus_run until [Extracted.entry + 0x168]
      all_goals first
        | (refine finF impl R b z bp ret hret s hwb2 hpre0 hz0 _ ?hsp ?h28 ?h29 ?h18 ?hrd1 ?hrd2 (s.mem.readLE (P + 8) 8) P 0 (s.mem.readLE (P + 24) 8) ?hfrA ?hpc ?h0 ?h1 ?h2 ?h3 (by omega) hcap.1 hcap.2 ?hPv hP rfl hPpa hPpb hPo hPd.symm hPb.symm hPz.symm hApa hApb hAo hAd.symm hAb'.symm hAz.symm hAP ?hword ?hnorm ?hzero ?hinv
           case hsp => rfl
           case h28 => simp [setReg_apply, h28]
           case h29 => simp [setReg_apply, h29]
           case h18 => simp [setReg_apply, h18]
           case hrd1 => rw [read_words4 _ _ _ _ _ _ _ _ (by omega)]; exact h_rd1
           case hrd2 => rw [read_words4 _ _ _ _ _ _ _ _ (by omega)]; exact h_rd2
           case hfrA => exact frame_words4 (frame_add hfr)
           case hpc => rfl
           case h0 => simp [setReg_apply]
           case h1 => simpa [setReg_apply] using h1
           case h2 => simp [setReg_apply]
           case h3 => simp [setReg_apply]
           case hPv => rw [read_words4 _ _ _ _ _ _ _ _ (by omega)]; exact h_rdP
           case hinv => rw [view_words4 _ _ _ _ _ _ _ _ hAo]; exact hinvS
           case hword =>
             intro i hi
             rw [words4 _ _ _ _ _ _ ?_ ?_ ?_ ?_ i hi]
             · obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
               all_goals (simp; try omega)
             all_goals (first | omega | simpa using Janus.Arm64.Memory.readLE_lt _ _ 8)
           case hnorm => simp; try omega
           case hzero =>
             intro i h1 h2
             obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
             all_goals (simp; try omega))
        | (refine finF impl R b z bp ret hret s hwb2 hpre0 hz0 _ ?hsp ?h28 ?h29 ?h18 ?hrd1 ?hrd2 (s.mem.readLE (P + 8) 8) P 1 (s.mem.readLE (P + 24) 8) ?hfrA ?hpc ?h0 ?h1 ?h2 ?h3 (by omega) hcap.1 hcap.2 ?hPv hP rfl hPpa hPpb hPo hPd.symm hPb.symm hPz.symm hApa hApb hAo hAd.symm hAb'.symm hAz.symm hAP ?hword ?hnorm ?hzero ?hinv
           case hsp => rfl
           case h28 => simp [setReg_apply, h28]
           case h29 => simp [setReg_apply, h29]
           case h18 => simp [setReg_apply, h18]
           case hrd1 => rw [read_words4 _ _ _ _ _ _ _ _ (by omega)]; exact h_rd1
           case hrd2 => rw [read_words4 _ _ _ _ _ _ _ _ (by omega)]; exact h_rd2
           case hfrA => exact frame_words4 (frame_add hfr)
           case hpc => rfl
           case h0 => simp [setReg_apply]
           case h1 => simpa [setReg_apply] using h1
           case h2 => simp [setReg_apply]
           case h3 => simp [setReg_apply]
           case hPv => rw [read_words4 _ _ _ _ _ _ _ _ (by omega)]; exact h_rdP
           case hinv => rw [view_words4 _ _ _ _ _ _ _ _ hAo]; exact hinvS
           case hword =>
             intro i hi
             rw [words4 _ _ _ _ _ _ ?_ ?_ ?_ ?_ i hi]
             · obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
               all_goals (simp; try omega)
             all_goals (first | omega | simpa using Janus.Arm64.Memory.readLE_lt _ _ 8)
           case hnorm => simp; try omega
           case hzero =>
             intro i h1 h2
             obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
             all_goals (simp; try omega))
        | (refine finF impl R b z bp ret hret s hwb2 hpre0 hz0 _ ?hsp ?h28 ?h29 ?h18 ?hrd1 ?hrd2 (s.mem.readLE (P + 8) 8) P 2 (s.mem.readLE (P + 24) 8) ?hfrA ?hpc ?h0 ?h1 ?h2 ?h3 (by omega) hcap.1 hcap.2 ?hPv hP rfl hPpa hPpb hPo hPd.symm hPb.symm hPz.symm hApa hApb hAo hAd.symm hAb'.symm hAz.symm hAP ?hword ?hnorm ?hzero ?hinv
           case hsp => rfl
           case h28 => simp [setReg_apply, h28]
           case h29 => simp [setReg_apply, h29]
           case h18 => simp [setReg_apply, h18]
           case hrd1 => rw [read_words4 _ _ _ _ _ _ _ _ (by omega)]; exact h_rd1
           case hrd2 => rw [read_words4 _ _ _ _ _ _ _ _ (by omega)]; exact h_rd2
           case hfrA => exact frame_words4 (frame_add hfr)
           case hpc => rfl
           case h0 => simp [setReg_apply]
           case h1 => simpa [setReg_apply] using h1
           case h2 => simp [setReg_apply]
           case h3 => simp [setReg_apply]
           case hPv => rw [read_words4 _ _ _ _ _ _ _ _ (by omega)]; exact h_rdP
           case hinv => rw [view_words4 _ _ _ _ _ _ _ _ hAo]; exact hinvS
           case hword =>
             intro i hi
             rw [words4 _ _ _ _ _ _ ?_ ?_ ?_ ?_ i hi]
             · obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
               all_goals (simp; try omega)
             all_goals (first | omega | simpa using Janus.Arm64.Memory.readLE_lt _ _ 8)
           case hnorm => simp; try omega
           case hzero =>
             intro i h1 h2
             obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
             all_goals (simp; try omega))
        | (refine finF impl R b z bp ret hret s hwb2 hpre0 hz0 _ ?hsp ?h28 ?h29 ?h18 ?hrd1 ?hrd2 (s.mem.readLE (P + 8) 8) P 3 (s.mem.readLE (P + 24) 8) ?hfrA ?hpc ?h0 ?h1 ?h2 ?h3 (by omega) hcap.1 hcap.2 ?hPv hP rfl hPpa hPpb hPo hPd.symm hPb.symm hPz.symm hApa hApb hAo hAd.symm hAb'.symm hAz.symm hAP ?hword ?hnorm ?hzero ?hinv
           case hsp => rfl
           case h28 => simp [setReg_apply, h28]
           case h29 => simp [setReg_apply, h29]
           case h18 => simp [setReg_apply, h18]
           case hrd1 => rw [read_words4 _ _ _ _ _ _ _ _ (by omega)]; exact h_rd1
           case hrd2 => rw [read_words4 _ _ _ _ _ _ _ _ (by omega)]; exact h_rd2
           case hfrA => exact frame_words4 (frame_add hfr)
           case hpc => rfl
           case h0 => simp [setReg_apply]
           case h1 => simpa [setReg_apply] using h1
           case h2 => simp [setReg_apply]
           case h3 => simp [setReg_apply]
           case hPv => rw [read_words4 _ _ _ _ _ _ _ _ (by omega)]; exact h_rdP
           case hinv => rw [view_words4 _ _ _ _ _ _ _ _ hAo]; exact hinvS
           case hword =>
             intro i hi
             rw [words4 _ _ _ _ _ _ ?_ ?_ ?_ ?_ i hi]
             · obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
               all_goals (simp; try omega)
             all_goals (first | omega | simpa using Janus.Arm64.Memory.readLE_lt _ _ 8)
           case hnorm => simp; try omega
           case hzero =>
             intro i h1 h2
             obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
             all_goals (simp; try omega))
        | (refine finF impl R b z bp ret hret s hwb2 hpre0 hz0 _ ?hsp ?h28 ?h29 ?h18 ?hrd1 ?hrd2 (s.mem.readLE (P + 8) 8) P 4 (s.mem.readLE (P + 24) 8) ?hfrA ?hpc ?h0 ?h1 ?h2 ?h3 (by omega) hcap.1 hcap.2 ?hPv hP rfl hPpa hPpb hPo hPd.symm hPb.symm hPz.symm hApa hApb hAo hAd.symm hAb'.symm hAz.symm hAP ?hword ?hnorm ?hzero ?hinv
           case hsp => rfl
           case h28 => simp [setReg_apply, h28]
           case h29 => simp [setReg_apply, h29]
           case h18 => simp [setReg_apply, h18]
           case hrd1 => rw [read_words4 _ _ _ _ _ _ _ _ (by omega)]; exact h_rd1
           case hrd2 => rw [read_words4 _ _ _ _ _ _ _ _ (by omega)]; exact h_rd2
           case hfrA => exact frame_words4 (frame_add hfr)
           case hpc => rfl
           case h0 => simp [setReg_apply]
           case h1 => simpa [setReg_apply] using h1
           case h2 => simp [setReg_apply]
           case h3 => simp [setReg_apply]
           case hPv => rw [read_words4 _ _ _ _ _ _ _ _ (by omega)]; exact h_rdP
           case hinv => rw [view_words4 _ _ _ _ _ _ _ _ hAo]; exact hinvS
           case hword =>
             intro i hi
             rw [words4 _ _ _ _ _ _ ?_ ?_ ?_ ?_ i hi]
             · obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
               all_goals (simp; try omega)
             all_goals (first | omega | simpa using Janus.Arm64.Memory.readLE_lt _ _ 8)
           case hnorm => simp; try omega
           case hzero =>
             intro i h1 h2
             obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
             all_goals (simp; try omega))
        | (refine finF impl R b z bp ret hret s hwb2 hpre0 hz0 _ ?hsp ?h28 ?h29 ?h18 ?hrd1 ?hrd2 (s.mem.readLE (P + 8) 8) P 0 (s.mem.readLE (P + 24) 8) ?hfrA ?hpc ?h0 ?h1 ?h2 ?h3 (by omega) hcap.1 hcap.2 ?hPv hP rfl hPpa hPpb hPo hPd.symm hPb.symm hPz.symm hApa hApb hAo hAd.symm hAb'.symm hAz.symm hAP ?hword ?hnorm ?hzero ?hinv
           case hsp => rfl
           case h28 => simp [setReg_apply, h28]
           case h29 => simp [setReg_apply, h29]
           case h18 => simp [setReg_apply, h18]
           case hrd1 => rw [read_words4 _ _ _ _ _ _ _ _ (by omega)]; exact h_rd1
           case hrd2 => rw [read_words4 _ _ _ _ _ _ _ _ (by omega)]; exact h_rd2
           case hfrA => exact frame_words4 (frame_add hfr)
           case hpc => rfl
           case h0 => simp [setReg_apply]
           case h1 => simpa [setReg_apply] using h1
           case h2 => simp [setReg_apply]
           case h3 => simp [setReg_apply]
           case hPv => rw [read_words4 _ _ _ _ _ _ _ _ (by omega)]; exact h_rdP
           case hinv => rw [view_words4 _ _ _ _ _ _ _ _ hAo]; exact hinvS
           case hword =>
             intro i hi
             rw [words4 _ _ _ _ _ _ ?_ ?_ ?_ ?_ i hi]
             · obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
               all_goals (simp; try omega)
             all_goals (first | omega | simpa using Janus.Arm64.Memory.readLE_lt _ _ 8)
           case hnorm => simp; try omega
           case hzero =>
             intro i h1 h2
             obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
             all_goals (simp; try omega))
    · sorry
  · sorry

end Fv256.Arm64.IntoBig
