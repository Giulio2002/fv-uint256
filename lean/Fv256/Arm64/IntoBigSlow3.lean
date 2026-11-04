import Fv256.Arm64.IntoBigFinF
import Fv256.Arm64.IntoBigClose
import Fv256.Arm64.IntoBigTail
import Fv256.Arm64.IntoBigLoop

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.IntoBig

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- The allocating path (`cap(words) < 4`): a fresh `[4]Word`, the copy, the normalization, the stores. -/
theorem slowHead3 (impl : List Segment) (R : RtInv) (b : Nat) (z bp : BitVec 64) (ret : Nat)
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
    (hfr : MemFrame s.mem S.mem (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 24), (bp.toNat, bp.toNat + 8)]))
    (hpc : S.pc = BitVec.ofNat 64 pcLoad) (h0 : S.regs 0 = z) (h1 : S.regs 1 = bp)
    (P c : Nat) (h_rdP : S.mem.readLE bp.toNat 8 = P) (h_rdc : S.mem.readLE (P + 24) 8 = c)
    (hc : c < 4)
    (hPa : s.mem.accessible P 32 true = true) (hP48 : P + 32 ≤ 2 ^ 48)
    (hgb : Apart bp.toNat 8 ((s.regs 28).toNat + 16) 8) (hgP : Apart P 32 ((s.regs 28).toNat + 16) 8)
    (hPd : Apart (s.sp.toNat - 4144) 4168 P 32) (hPb : Apart bp.toNat 8 P 32) (hPz : Apart z.toNat 32 P 32)
    (L0 : List (Nat × Nat)) (b0 : Nat)
    (hLP : (L0 = [] ∧ Outside P 32 R.rt) ∨ (L0 = [(P, P + 32)] ∧ InRanges P 32 R.rt))
    (hPs : (L0 = [] ∧ s.mem.readLE bp.toNat 8 = P ∧ P ≠ 0) ∨ (L0 = [(P, P + 32)] ∧ s.mem.readLE bp.toNat 8 = 0))
    (hinv : R.inv b0 L0 (s.regs 28).toNat (view R.rt L0 S.mem)) (hb0 : 32 ≤ b0)
    (hPfr : InRanges P 32 (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 24), (bp.toNat, bp.toNat + 8),
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
    obtain ⟨hPs1, hP0⟩ : s.mem.readLE bp.toNat 8 = P ∧ P ≠ 0 := by
      rcases hPs with ⟨-, h, h'⟩ | ⟨h, -⟩
      · exact ⟨h, h'⟩
      · simp at h
    janus_run until [pcLoopHead] calls [hnew.pos]
    unfold Hidden at hfacts
    obtain ⟨hzb', hzo', hPb', hPz', hbpo', hbpd', hzd'⟩ := hfacts
    rename_i w6 w5 w4 w3 w2 w1 w0 hLive hMF hT1 hInR hLe hAcc hM8 hM16 hZB hT2 hAp hInv ha1 ha2 ha3 ha4 ha5
    have hzr := s2_zr hMF hfr hb' hzo' hzd' hzb'
    have hwd : ∀ i, i < 4 → (((((w2.writeLE (BitVec.toNat w6) 8 (w2.readLE z.toNat 8)).writeLE (BitVec.toNat w6 + 8) 8
        (w2.readLE (z.toNat + 8) 8)).writeLE (BitVec.toNat w6 + 16) 8 (w2.readLE (z.toNat + 16) 8)).writeLE
        (BitVec.toNat w6 + 24) 8 (w2.readLE (z.toNat + 24) 8)).readLE (BitVec.toNat w6 + 8 * i) 8)
        = s.mem.readLE (z.toNat + 8 * i) 8 :=
      s2_word hzr (Memory.readLE_lt _ _ 8) (Memory.readLE_lt _ _ 8) (Memory.readLE_lt _ _ 8) (Memory.readLE_lt _ _ 8)
        (fun k hk => by obtain rfl | rfl | rfl | rfl := lt4_cases k hk <;> rfl)
    refine normloop impl ret hret _ (BitVec.toNat w6) (fun i => s.mem.readLE (z.toNat + 8 * i) 8) (le48 _ hLe) 4 (by decide) _ rfl
      (by simp [setReg_apply, callRegs_apply]) (by simp [setReg_apply])
      (by simp only [Memory.accessible_writeLE]; rw [hMF.accessible, hfr.accessible]; exact Memory.accessible_weaken _ hAcc)
      hwd ?_
    intro S2 len hl hn hz hp hr0 hr1 hsp hm hr
    have hw6 : (S2.regs 0).toNat = BitVec.toNat w6 := by rw [hr0]; simp [setReg_apply, callRegs_apply]
    refine reaches_mono (slowTail impl R b (b0 - 32) z bp ret hret s hwb2 hpre0 hz0 S2 s.mem hsp
      (by rw [hr 28 (by decide) (by decide) (by decide)]; simp [setReg_apply, callRegs_apply, h28])
      (by rw [hr 29 (by decide) (by decide) (by decide)]; simp [setReg_apply, callRegs_apply, h29])
      (by rw [hr 18 (by decide) (by decide) (by decide)]; simp [setReg_apply, callRegs_apply, h18])
      (by rw [hm]; exact (s2_slot hMF hout ha1 hb' (by omega) (by omega) (Or.inl (by omega))).trans h_rd1)
      (by rw [hm]; exact (s2_slot hMF hout ha1 hb' (by omega) (by omega) (Or.inl (by omega))).trans h_rd2)
      (by rw [hm]; exact (s2_slot hMF hout ha1 hb' (by omega) (by omega) (Or.inr (by omega))).trans h_rd3)
      (by rw [hm]; exact (s2_slot hMF hout ha1 hb' (by omega) (by omega) (Or.inr (by omega))).trans h_rd4)
      (by rw [hm]; exact frame_s2 hb' hMF hfr hInR) hp _ _ _ hw6 (by rw [hr1]; try exact tn len hl) hl
      (by rw [hm]; exact (s2_bp hMF hbpo' hbpd' ha5 hb').trans h_rdP)
      hPa hP48 hAcc (le48 _ hLe) hPd ha1 hgP (Or.symm ha2) (Or.symm h_apart) hPb' (by rw [hm]; exact hwd)
      hn (fun i h1 h2 => hz i h1 h2) [] (Or.inl ⟨rfl, hX⟩)
      (by rw [hm]; rw [view_words4_live _ _ _ _ _ _ _ _ ⟨(BitVec.toNat w6, BitVec.toNat w6 + 32), by simp, Nat.le_refl _, Nat.le_refl _⟩]; exact hInv))
      (fun o ho => post_of_tail R z bp s P hz0 ?hn o ho ?hw)
    case hn => exact fun h0 => absurd (hPs1.symm.trans h0) hP0
    case hw =>
      intro a n hh
      simp only [outside_append, outside_cons, outside_nil, and_true] at hh ⊢
      rw [hPs1] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1⟩
  · subst hL
    have hPs1 : s.mem.readLE bp.toNat 8 = 0 := by
      rcases hPs with ⟨h, -, -⟩ | ⟨-, h⟩
      · simp at h
      · exact h
    janus_run until [pcLoopHead] calls [hnew.pos]
    unfold Hidden at hfacts
    obtain ⟨hzb', hzo', hPb', hPz', hbpo', hbpd', hzd'⟩ := hfacts
    rename_i w6 w5 w4 w3 w2 w1 w0 hLive hMF hPw hInR hLe hAcc hM8 hM16 hZB hT2 hAp hInv ha1 ha2 ha3 ha4
    have hzr := s2_zr hMF hfr hb' hzo' hzd' hzb'
    have hwd : ∀ i, i < 4 → (((((w2.writeLE (BitVec.toNat w6) 8 (w2.readLE z.toNat 8)).writeLE (BitVec.toNat w6 + 8) 8
        (w2.readLE (z.toNat + 8) 8)).writeLE (BitVec.toNat w6 + 16) 8 (w2.readLE (z.toNat + 16) 8)).writeLE
        (BitVec.toNat w6 + 24) 8 (w2.readLE (z.toNat + 24) 8)).readLE (BitVec.toNat w6 + 8 * i) 8)
        = s.mem.readLE (z.toNat + 8 * i) 8 :=
      s2_word hzr (Memory.readLE_lt _ _ 8) (Memory.readLE_lt _ _ 8) (Memory.readLE_lt _ _ 8) (Memory.readLE_lt _ _ 8)
        (fun k hk => by obtain rfl | rfl | rfl | rfl := lt4_cases k hk <;> rfl)
    refine normloop impl ret hret _ (BitVec.toNat w6) (fun i => s.mem.readLE (z.toNat + 8 * i) 8) (le48 _ hLe) 4 (by decide) _ rfl
      (by simp [setReg_apply, callRegs_apply]) (by simp [setReg_apply])
      (by simp only [Memory.accessible_writeLE]; rw [hMF.accessible, hfr.accessible]; exact Memory.accessible_weaken _ hAcc)
      hwd ?_
    intro S2 len hl hn hz hp hr0 hr1 hsp hm hr
    have hw6 : (S2.regs 0).toNat = BitVec.toNat w6 := by rw [hr0]; simp [setReg_apply, callRegs_apply]
    refine reaches_mono (slowTail impl R b (b0 - 32) z bp ret hret s hwb2 hpre0 hz0 S2 s.mem hsp
      (by rw [hr 28 (by decide) (by decide) (by decide)]; simp [setReg_apply, callRegs_apply, h28])
      (by rw [hr 29 (by decide) (by decide) (by decide)]; simp [setReg_apply, callRegs_apply, h29])
      (by rw [hr 18 (by decide) (by decide) (by decide)]; simp [setReg_apply, callRegs_apply, h18])
      (by rw [hm]; exact (s2_slot hMF hout ha1 hb' (by omega) (by omega) (Or.inl (by omega))).trans h_rd1)
      (by rw [hm]; exact (s2_slot hMF hout ha1 hb' (by omega) (by omega) (Or.inl (by omega))).trans h_rd2)
      (by rw [hm]; exact (s2_slot hMF hout ha1 hb' (by omega) (by omega) (Or.inr (by omega))).trans h_rd3)
      (by rw [hm]; exact (s2_slot hMF hout ha1 hb' (by omega) (by omega) (Or.inr (by omega))).trans h_rd4)
      (by rw [hm]; exact frame_s2 hb' hMF hfr hInR) hp _ _ _ hw6 (by rw [hr1]; try exact tn len hl) hl
      (by rw [hm]; exact (s2_bp hMF hbpo' hbpd' h_apart hb').trans h_rdP)
      hPa hP48 hAcc (le48 _ hLe) hPd ha1 hgP (Or.symm ha2) hPw hPb' (by rw [hm]; exact hwd)
      hn (fun i h1 h2 => hz i h1 h2) [(P, P + 32)] (Or.inr ⟨rfl, hX⟩)
      (by rw [hm]; rw [view_words4_live _ _ _ _ _ _ _ _ ⟨(BitVec.toNat w6, BitVec.toNat w6 + 32), by simp, Nat.le_refl _, Nat.le_refl _⟩]; exact hInv))
      (fun o ho => post_of_tail R z bp s P hz0 ?hn o ho ?hw)
    case hn =>
      intro _ a n hh
      simp only [outside_append, outside_cons, outside_nil, and_true] at hh ⊢
      obtain ⟨r, hr', hr1', hr2'⟩ := hX
      have hro := MemFrame.outside_mem hh.1 hr'
      refine ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2, ?_⟩
      omega
    case hw =>
      intro a n hh
      simp only [outside_append, outside_cons, outside_nil, and_true] at hh ⊢
      obtain ⟨r, hr', hr1', hr2'⟩ := hX
      have hro := MemFrame.outside_mem hh.1 hr'
      refine ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, ?_⟩
      omega

end Fv256.Arm64.IntoBig
