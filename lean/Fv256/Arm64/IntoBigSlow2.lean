import Fv256.Arm64.IntoBigFinF
import Fv256.Arm64.IntoBigClose
import Fv256.Arm64.IntoBigTail

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.IntoBig

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option profiler true in
set_option profiler.threshold 500 in
/-- The allocating path (`cap(words) < 4`): a fresh `[4]Word`, the copy, the normalization, the stores. -/
theorem slowHead (impl : List Segment) (R : RtInv) (b : Nat) (z bp : BitVec 64) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret) (s : State)
    (hnew : NewobjectLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb2 : WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hpre : Pre R b z bp s) (hz0 : z.toNat ≠ 0)
    (S : State) (hsp : S.sp = s.sp - 48#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 56#64)
    (h18 : S.regs 18 = s.regs 18) (h_rd1 : S.mem.readLE (s.sp.toNat - 48) 8 = ret)
    (h_rd2 : S.mem.readLE (s.sp.toNat - 56) 8 = (s.regs 29).toNat)
    (h_rd3 : S.mem.readLE (s.sp.toNat + 8) 8 = z.toNat) (h_rd4 : S.mem.readLE (s.sp.toNat + 16) 8 = bp.toNat)
    (hfr : MemFrame s.mem S.mem (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24), (bp.toNat, bp.toNat + 8)]))
    (hpc : S.pc = BitVec.ofNat 64 pcLoad) (h0 : S.regs 0 = z) (h1 : S.regs 1 = bp)
    (P c : Nat) (h_rdP : S.mem.readLE bp.toNat 8 = P) (h_rdc : S.mem.readLE (P + 24) 8 = c)
    (hc : c < 4)
    (hPa : s.mem.accessible P 32 true = true) (hP48 : P + 32 ≤ 2 ^ 48)
    (hgb : Apart bp.toNat 8 ((s.regs 28).toNat + 16) 8) (hgP : Apart P 32 ((s.regs 28).toNat + 16) 8)
    (hPd : Apart (s.sp.toNat - 4144) 4168 P 32) (hPb : Apart bp.toNat 8 P 32) (hPz : Apart z.toNat 32 P 32)
    (L0 : List (Nat × Nat)) (b0 : Nat)
    (hLP : (L0 = [] ∧ Outside P 32 R.rt) ∨ (L0 = [(P, P + 32)] ∧ InRanges P 32 R.rt))
    (hPs : (L0 = [] ∧ s.mem.readLE bp.toNat 8 = P) ∨ (L0 = [(P, P + 32)] ∧ s.mem.readLE bp.toNat 8 = 0))
    (hinv : R.inv b0 L0 (s.regs 28).toNat (view R.rt L0 S.mem)) (hb0 : 32 ≤ b0)
    (hPfr : InRanges P 32 (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24), (bp.toNat, bp.toNat + 8),
      (s.mem.readLE bp.toNat 8, s.mem.readLE bp.toNat 8 + 32),
      (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8, s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8 + 32)])) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R z bp s s') := by
  have hpre0 := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hflag, hty1, hty2, hok1, hok2, hok3, hok4,
    hinv0, hbud, ⟨hbpa, hbpb⟩, hbpo, hbpd, hz⟩ := hpre
  obtain ⟨hzp, hzo, hzd, hzb, hzP⟩ := hz hz0
  obtain ⟨hzpa, hzpb⟩ := hzp
  have hret48 := hret.user
  have hret4 := hret.aligned
  have hspn : S.sp.toNat = s.sp.toNat - 48 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hblk := Janus.Contracts.AllocSat.le_blockSize 32 true
  unfold Apart at hPd hga hgb hgP
  simp only [Disjoint] at hbpd
  have hfacts : Hidden (Disjoint z.toNat 32 bp.toNat 8 ∧ Outside z.toNat 32 R.rt ∧ Apart bp.toNat 8 P 32 ∧
      Apart z.toNat 32 P 32 ∧ Outside bp.toNat 8 R.rt ∧ Disjoint bp.toNat 8 (s.sp.toNat - 4144) 4168 ∧
      Disjoint z.toNat 32 (s.sp.toNat - 4144) 4168) :=
    ⟨hzb, hzo, hPb, hPz, hbpo, hbpd, hzd⟩
  clear hzP hz hzd hzb hPb hPz hzo hinv0 hbud
  janus_data hd [hw, hbpa, hPa]
  janus_eval_nat h_b : bigType
  janus_eval_nat h_a : arrType
  janus_eval_nat h_f : flagAddr
  rw [h_b] at hty1 hok1
  rw [h_a] at hty2 hok2
  rw [h_f] at hflag
  have hbs : blockSize 32 true = 32 := by decide
  rw [hbs] at hblk
  rcases hLP with ⟨hL, hX⟩ | ⟨hL, hX⟩
  · subst hL
    have hPs1 : s.mem.readLE bp.toNat 8 = P := by
      rcases hPs with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · simp at h
    try (have hPsa := hX.apart hout; unfold Apart at hPsa)
    janus_run until [pcTail] calls [hnew.pos]
    all_goals (unfold Hidden at hfacts; obtain ⟨hzb', hzo', hPb', hPz', hbpo', hbpd', hzd'⟩ := hfacts)
    all_goals (
      refine reaches_mono (slowTail impl R b (b0 - 32) z bp ret hret s hwb2 hpre0 hz0 _ s.mem rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ P _ rfl rfl ?_ ?_ hPa hP48 ?_ ?_ hPd ?_ hgP ?_ ?_ ?_ ?_ ?_ ?_ [] ?_ ?_) (fun o ho => post_of_tail R z bp s P hz0 o ho ?_)
      · dsimp only; simp [setReg_apply, callRegs_apply, h28]
      · dsimp only; simp [setReg_apply, callRegs_apply, h29]
      · dsimp only; simp [setReg_apply, callRegs_apply, h18]
      · dsimp only; rw [read_words4 _ _ _ _ _ _ _ _ (by unfold Apart at *; omega), read_call ‹MemFrame S.mem _ _› (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact h_rd1
      · dsimp only; rw [read_words4 _ _ _ _ _ _ _ _ (by unfold Apart at *; omega), read_call ‹MemFrame S.mem _ _› (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact h_rd2
      · dsimp only; rw [read_words4 _ _ _ _ _ _ _ _ (by unfold Apart at *; omega), read_call ‹MemFrame S.mem _ _› (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact h_rd3
      · dsimp only; rw [read_words4 _ _ _ _ _ _ _ _ (by unfold Apart at *; omega), read_call ‹MemFrame S.mem _ _› (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact h_rd4
      · dsimp only; exact frame_s2 (by omega) ‹MemFrame S.mem _ _› hfr ‹InRanges (BitVec.toNat _) 32 R.rt›
      · rfl
      · dsimp only; simp [setReg_apply, callRegs_apply]
      · dsimp only; rw [read_words4 _ _ _ _ _ _ _ _ (by unfold Apart at *; omega), read_call ‹MemFrame S.mem _ _› hbpo (by omega) (by omega)]; exact h_rdP
      · dsimp only; simp [setReg_apply, callRegs_apply]; exact ‹s.mem.accessible (BitVec.toNat _) 32 true = true›
      · dsimp only; simp [setReg_apply, callRegs_apply]; omega
      · dsimp only; simp [setReg_apply, callRegs_apply]; exact ‹Apart (BitVec.toNat s.sp - 4144) 4168 (BitVec.toNat _) 32›
      · dsimp only; simp [setReg_apply, callRegs_apply]; exact Or.symm ‹Apart (BitVec.toNat (s.regs 28) + 16) 8 (BitVec.toNat _) 32›
      · dsimp only; simp [setReg_apply, callRegs_apply]; exact Or.symm ‹Apart P 32 (BitVec.toNat _) 32›
      · exact hPb'
      · dsimp only; simp [setReg_apply, callRegs_apply]
        have hzr := s2_zr ‹MemFrame S.mem _ _› hfr hb' hzo' hzd' hzb'
        have hz0 := hzr 0 (by decide)
        have hz1 := hzr 1 (by decide)
        have hz2 := hzr 2 (by decide)
        have hz3 := hzr 3 (by decide)
        simp only [Nat.reduceMul, Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hz0 hz1 hz2 hz3
        exact s2_word hzr (by first | exact Nat.two_pow_pos 64 | simpa using Janus.Arm64.Memory.readLE_lt _ _ 8) (by first | exact Nat.two_pow_pos 64 | simpa using Janus.Arm64.Memory.readLE_lt _ _ 8) (by first | exact Nat.two_pow_pos 64 | simpa using Janus.Arm64.Memory.readLE_lt _ _ 8) (by first | exact Nat.two_pow_pos 64 | simpa using Janus.Arm64.Memory.readLE_lt _ _ 8)
          (by intro k hk; obtain rfl | rfl | rfl | rfl := lt4_cases k hk
              all_goals first | rfl | exact (‹Memory.readLE _ z.toNat 8 = 0›).symm | exact (‹Memory.readLE _ (z.toNat + 8) 8 = 0›).symm | exact (‹Memory.readLE _ (z.toNat + 16) 8 = 0›).symm | exact (‹Memory.readLE _ (z.toNat + 24) 8 = 0›).symm)
      · dsimp only; simp [setReg_apply, callRegs_apply] <;> (
          have hzr := s2_zr ‹MemFrame S.mem _ _› hfr hb' hzo' hzd' hzb'
          have hz0 := hzr 0 (by decide)
          have hz1 := hzr 1 (by decide)
          have hz2 := hzr 2 (by decide)
          have hz3 := hzr 3 (by decide)
          simp only [Nat.reduceMul, Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hz0 hz1 hz2 hz3
          first | (rw [← hz0]; exact ‹¬ Memory.readLE _ z.toNat 8 = 0›) | (rw [← hz1]; exact ‹¬ Memory.readLE _ (z.toNat + 8) 8 = 0›) | (rw [← hz2]; exact ‹¬ Memory.readLE _ (z.toNat + 16) 8 = 0›) | (rw [← hz3]; exact ‹¬ Memory.readLE _ (z.toNat + 24) 8 = 0›))
      · dsimp only; simp [setReg_apply, callRegs_apply] <;> (
          have hzr := s2_zr ‹MemFrame S.mem _ _› hfr hb' hzo' hzd' hzb'
          have hz0 := hzr 0 (by decide)
          have hz1 := hzr 1 (by decide)
          have hz2 := hzr 2 (by decide)
          have hz3 := hzr 3 (by decide)
          simp only [Nat.reduceMul, Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hz0 hz1 hz2 hz3
          intro i h1 h2
          obtain rfl | rfl | rfl | rfl := lt4_cases i h2 <;> (simp only [Nat.reduceMul, Nat.mul_zero, Nat.add_zero, Nat.mul_one]; first | (rw [← hz0]; exact ‹Memory.readLE _ z.toNat 8 = 0›) | (rw [← hz1]; exact ‹Memory.readLE _ (z.toNat + 8) 8 = 0›) | (rw [← hz2]; exact ‹Memory.readLE _ (z.toNat + 16) 8 = 0›) | (rw [← hz3]; exact ‹Memory.readLE _ (z.toNat + 24) 8 = 0›)))
      · exact Or.inl ⟨rfl, hX⟩
      · dsimp only; simp [setReg_apply, callRegs_apply]
        rw [view_words4_live _ _ _ _ _ _ _ _ ⟨(BitVec.toNat _, BitVec.toNat _ + 32), by simp, Nat.le_refl _, Nat.le_refl _⟩]
        exact ‹R.inv _ _ _ _›
      · intro a n hh
        simp only [outside_append, outside_cons, outside_nil, and_true] at hh ⊢
        rw [hPs1] at hh
        exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩)
  · subst hL
    have hPs1 : s.mem.readLE bp.toNat 8 = 0 := by
      rcases hPs with ⟨h, -⟩ | ⟨-, h⟩
      · simp at h
      · exact h
    try (have hPsa := hX.apart hout; unfold Apart at hPsa)
    janus_run until [pcTail] calls [hnew.pos]
    all_goals (unfold Hidden at hfacts; obtain ⟨hzb', hzo', hPb', hPz', hbpo', hbpd', hzd'⟩ := hfacts)
    all_goals (
      refine reaches_mono (slowTail impl R b (b0 - 32) z bp ret hret s hwb2 hpre0 hz0 _ s.mem rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ P _ rfl rfl ?_ ?_ hPa hP48 ?_ ?_ hPd ?_ hgP ?_ ?_ ?_ ?_ ?_ ?_ [(P, P + 32)] ?_ ?_) (fun o ho => post_of_tail R z bp s P hz0 o ho ?_)
      · dsimp only; simp [setReg_apply, callRegs_apply, h28]
      · dsimp only; simp [setReg_apply, callRegs_apply, h29]
      · dsimp only; simp [setReg_apply, callRegs_apply, h18]
      · dsimp only; rw [read_words4 _ _ _ _ _ _ _ _ (by unfold Apart at *; omega), read_call ‹MemFrame S.mem _ _› (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact h_rd1
      · dsimp only; rw [read_words4 _ _ _ _ _ _ _ _ (by unfold Apart at *; omega), read_call ‹MemFrame S.mem _ _› (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact h_rd2
      · dsimp only; rw [read_words4 _ _ _ _ _ _ _ _ (by unfold Apart at *; omega), read_call ‹MemFrame S.mem _ _› (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact h_rd3
      · dsimp only; rw [read_words4 _ _ _ _ _ _ _ _ (by unfold Apart at *; omega), read_call ‹MemFrame S.mem _ _› (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]; exact h_rd4
      · dsimp only; exact frame_s2 (by omega) ‹MemFrame S.mem _ _› hfr ‹InRanges (BitVec.toNat _) 32 R.rt›
      · rfl
      · dsimp only; simp [setReg_apply, callRegs_apply]
      · dsimp only; rw [read_words4 _ _ _ _ _ _ _ _ (by unfold Apart at *; omega), read_call ‹MemFrame S.mem _ _› hbpo (by omega) (by omega)]; exact h_rdP
      · dsimp only; simp [setReg_apply, callRegs_apply]; exact ‹s.mem.accessible (BitVec.toNat _) 32 true = true›
      · dsimp only; simp [setReg_apply, callRegs_apply]; omega
      · dsimp only; simp [setReg_apply, callRegs_apply]; exact ‹Apart (BitVec.toNat s.sp - 4144) 4168 (BitVec.toNat _) 32›
      · dsimp only; simp [setReg_apply, callRegs_apply]; exact Or.symm ‹Apart (BitVec.toNat (s.regs 28) + 16) 8 (BitVec.toNat _) 32›
      · dsimp only; simp [setReg_apply, callRegs_apply]; exact Or.symm ‹Apart P 32 (BitVec.toNat _) 32›
      · exact hPb'
      · dsimp only; simp [setReg_apply, callRegs_apply]
        have hzr := s2_zr ‹MemFrame S.mem _ _› hfr hb' hzo' hzd' hzb'
        have hz0 := hzr 0 (by decide)
        have hz1 := hzr 1 (by decide)
        have hz2 := hzr 2 (by decide)
        have hz3 := hzr 3 (by decide)
        simp only [Nat.reduceMul, Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hz0 hz1 hz2 hz3
        exact s2_word hzr (by first | exact Nat.two_pow_pos 64 | simpa using Janus.Arm64.Memory.readLE_lt _ _ 8) (by first | exact Nat.two_pow_pos 64 | simpa using Janus.Arm64.Memory.readLE_lt _ _ 8) (by first | exact Nat.two_pow_pos 64 | simpa using Janus.Arm64.Memory.readLE_lt _ _ 8) (by first | exact Nat.two_pow_pos 64 | simpa using Janus.Arm64.Memory.readLE_lt _ _ 8)
          (by intro k hk; obtain rfl | rfl | rfl | rfl := lt4_cases k hk
              all_goals first | rfl | exact (‹Memory.readLE _ z.toNat 8 = 0›).symm | exact (‹Memory.readLE _ (z.toNat + 8) 8 = 0›).symm | exact (‹Memory.readLE _ (z.toNat + 16) 8 = 0›).symm | exact (‹Memory.readLE _ (z.toNat + 24) 8 = 0›).symm)
      · dsimp only; simp [setReg_apply, callRegs_apply] <;> (
          have hzr := s2_zr ‹MemFrame S.mem _ _› hfr hb' hzo' hzd' hzb'
          have hz0 := hzr 0 (by decide)
          have hz1 := hzr 1 (by decide)
          have hz2 := hzr 2 (by decide)
          have hz3 := hzr 3 (by decide)
          simp only [Nat.reduceMul, Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hz0 hz1 hz2 hz3
          first | (rw [← hz0]; exact ‹¬ Memory.readLE _ z.toNat 8 = 0›) | (rw [← hz1]; exact ‹¬ Memory.readLE _ (z.toNat + 8) 8 = 0›) | (rw [← hz2]; exact ‹¬ Memory.readLE _ (z.toNat + 16) 8 = 0›) | (rw [← hz3]; exact ‹¬ Memory.readLE _ (z.toNat + 24) 8 = 0›))
      · dsimp only; simp [setReg_apply, callRegs_apply] <;> (
          have hzr := s2_zr ‹MemFrame S.mem _ _› hfr hb' hzo' hzd' hzb'
          have hz0 := hzr 0 (by decide)
          have hz1 := hzr 1 (by decide)
          have hz2 := hzr 2 (by decide)
          have hz3 := hzr 3 (by decide)
          simp only [Nat.reduceMul, Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hz0 hz1 hz2 hz3
          intro i h1 h2
          obtain rfl | rfl | rfl | rfl := lt4_cases i h2 <;> (simp only [Nat.reduceMul, Nat.mul_zero, Nat.add_zero, Nat.mul_one]; first | (rw [← hz0]; exact ‹Memory.readLE _ z.toNat 8 = 0›) | (rw [← hz1]; exact ‹Memory.readLE _ (z.toNat + 8) 8 = 0›) | (rw [← hz2]; exact ‹Memory.readLE _ (z.toNat + 16) 8 = 0›) | (rw [← hz3]; exact ‹Memory.readLE _ (z.toNat + 24) 8 = 0›)))
      · exact Or.inr ⟨rfl, hX⟩
      · dsimp only; simp [setReg_apply, callRegs_apply]
        rw [view_words4_live _ _ _ _ _ _ _ _ ⟨(BitVec.toNat _, BitVec.toNat _ + 32), by simp, Nat.le_refl _, Nat.le_refl _⟩]
        exact ‹R.inv _ _ _ _›
      · intro a n hh
        simp only [outside_append, outside_cons, outside_nil, and_true] at hh ⊢
        obtain ⟨r, hr, hr1, hr2⟩ := hX
        have hro := MemFrame.outside_mem hh.1 hr
        refine ⟨hh.1, hh.2.1, hh.2.2.1, ?_⟩
        omega)

end Fv256.Arm64.IntoBig
