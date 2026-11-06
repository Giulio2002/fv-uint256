import Fv256.Arm64.MarshalSSZAppendG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Fv256.Msa

namespace Fv256.Arm64.MarshalSSZAppendG

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem blk1 (impl : List Segment) (R : RtInv) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret)
    (hg : RtLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive)
    (s S : State) (z : BitVec 64) (dp len0 cap0 b b0 : Nat) (len pp cc : BitVec 64) (L L0 : List (Nat × Nat))
    (Q : Outcome → Prop)
    (hal : s.sp.toNat % 16 = 0) (hb' : 4232 ≤ s.sp.toNat) (ha : s.sp.toNat + 40 ≤ 2 ^ 48)
    (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48) (hg2 : s.mem.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hg3 : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 4224 < s.sp.toNat)
    (hzp : s.mem.accessible z.toNat 32 false = true) (hz48 : z.toNat + 32 ≤ 2 ^ 48)
    (hzd : Disjoint z.toNat 32 (s.sp.toNat - 4232) 4272)
    (hout : Outside (s.sp.toNat - 4232) 4272 R.rt)
    (hga : Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4232) 4272)
    (hgr : Outside ((s.regs 28).toNat + 16) 8 R.rt)
    (hdt : Apart u8T 16 (s.sp.toNat - 4232) 4272)
    (hgd : Apart ((s.regs 28).toNat + 16) 8 dp cap0) (hdtd : Apart u8T 16 dp cap0)
    (hd : Extracted.program.DataLoaded s.mem) (hdesc : DescOK R u8T)
    (hl0 : len.toNat = len0 + 8) (hk : len.toNat + 8 ≤ len0 + 32) (hl0b : len0 < 2 ^ 40)
    (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x70))
    (m : Nat) (hI : BI R s S z ret dp len0 cap0 b0 L0 len pp cc b L (m + 1))
    (hcont : ∀ (S' : State) (pp' cc' : BitVec 64) (b' : Nat) (L' : List (Nat × Nat)),
      S'.pc = BitVec.ofNat 64 (Extracted.entry + 0xbc) →
      BI R s S' z ret dp len0 cap0 b0 L0 (len + 8#64) pp' cc' b' L' m → b - Kc len0 ≤ b' →
      Reaches ((Extracted.program.link impl).withExit ret) S' Q) :
    Reaches ((Extracted.program.link impl).withExit ret) S Q := by
  obtain ⟨hsp, h0, h1, h3, h5, h18, h28, h29, hrd1, hrd2, hrd3, hw, hfr, hng, hzs, hinv, hLs, hzL, hzpd, hlge, hlle, hlc, hC, hPb,
    hdj, hroom, hgrow, hbud, hrdy, hwho, hpre, hmid⟩ := hI
  have hlen8 : (len + 8#64).toNat = len.toNat + 8 := by
    rw [BitVec.toNat_add]; simp; omega
  have hz8 : S.mem.readLE (z.toNat + 8) 8 = s.mem.readLE (z.toNat + 8) 8 := hzs 1 (by omega)
  by_cases hl : len.toNat + 8 ≤ cc.toNat
  · obtain ⟨hacc, hdest⟩ := hroom hl
    have hap : Apart (pp.toNat + len.toNat) 8 (s.sp.toNat - 4232) 4272 := by
      unfold Apart at hdj ⊢; omega
    have hin : InRanges (pp.toNat + len.toNat) 8 (R.rt ++ [(s.sp.toNat - 4232, s.sp.toNat + 40), (dp, dp + cap0)]) := by
      rcases hwho with ⟨h1, h2⟩ | ⟨r, hr, h1, h2⟩
      · exact ⟨(dp, dp + cap0), by simp, by simp only []; omega, by simp only []; omega⟩
      · exact ⟨r, by simp [hr], by omega, by omega⟩
    janus_data hd [hw, hacc]
    janus_run until [Extracted.entry + 0xbc]
    refine hcont _ pp cc b L (by first | rfl | decide) ?_ (by omega)
    have hacc8 : S.mem.accessible (pp.toNat + len.toNat) 8 true = true :=
      Memory.accessible_sub S.mem hacc (Or.inr rfl) (by omega) (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [setReg, h0]
    · simp [setReg, h1]
    · simp [setReg, h3]
    · simp [setReg]; bv_omega
    · simp [setReg, h18]
    · simp [setReg, h28]
    · simp [setReg, h29]
    · dsimp only; rw [Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hap; omega)]; exact hrd1
    · dsimp only; rw [Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hap; omega)]; exact hrd2
    · dsimp only; rw [Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hap; omega)]; exact hrd3
    · dsimp only; rw [Memory.accessible_writeLE]; exact hw
    · exact hfr.writeLE_inRanges _ hin
    · intro hng'
      obtain ⟨h1', h2', h3', h4', h5'⟩ := hng hng'
      refine ⟨h1', h2', h3', h4', ?_⟩
      have h3w := h5'.mono (rs' := [(dp + len0, dp + len.toNat + 8), (s.sp.toNat - 4232, s.sp.toNat + 40)]) (by
        intro a n ho
        simp only [outside_cons, outside_nil, and_true] at ho ⊢
        omega)
      exact (h3w.writeLE_inRanges _ ⟨(dp + len0, dp + len.toNat + 8), by simp, by omega, by omega⟩).mono (by
        intro a n ho
        simp only [outside_cons, outside_nil, and_true] at ho ⊢
        omega)
    · intro i hi; dsimp only
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hzpd; omega)]; exact hzs i hi
    · dsimp only
      rcases hdest with ⟨r, hr, h1, h2⟩ | h
      · rw [view_writeLE_live ⟨r, hr, by omega, by omega⟩]; exact hinv
      · rw [view_writeLE_out (Outside.of_sub h (by omega) (by omega))]; exact hinv
    · exact hLs
    · exact hzL
    · exact hzpd
    · rw [hlen8]; omega
    · rw [hlen8]; omega
    · rw [hlen8]; omega
    · exact hC
    · exact hPb
    · exact hdj
    · intro _; dsimp only; rw [Memory.accessible_writeLE]; exact ⟨hacc, hdest⟩
    · intro _ h0'; dsimp only; rw [Memory.accessible_writeLE]
      exact Memory.accessible_sub S.mem hacc (Or.inl rfl) (Nat.le_refl _) (by rw [hlen8] at *; omega)
    · exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_succ m)) hbud
    · rw [hlen8]; exact hrdy.2 hl
    · exact hwho
    · intro i hi; dsimp only
      rw [Memory.bytes_writeLE_outside _ (Or.inl (by omega))]; exact hpre i hi
    · dsimp only
      have h1 : len.toNat + 8 - len0 = (len.toNat - len0) + 8 := by omega
      have h2 : pp.toNat + len.toNat = pp.toNat + len0 + (len.toNat - len0) := by omega
      rw [hlen8, h1, h2]
      exact mid_step S.mem s.mem (pp.toNat + len0) (len.toNat - len0) z.toNat _ hmid
        (by rw [Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _), show z.toNat + (len.toNat - len0) = z.toNat + 8 by omega]; exact hz8)
  · obtain ⟨hrd⟩ := (⟨hgrow (by omega)⟩ : Nonempty _)
    have hcostK := cost_le len0 len.toNat cc.toNat (by omega) (by omega)
    have hK : Kc len0 ≤ b := by rw [Nat.succ_mul] at hbud; omega
    have hcost : roundupsize (nextslicecap (len.toNat + 8) cc.toNat) true ≤ b := Nat.le_trans hcostK hK
    have hgS : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
      hfr.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        refine ⟨hgr, ?_, ?_⟩ <;> (unfold Apart at hga hgd; omega))
    have hg3' : S.mem.readLE ((s.regs 28).toNat + 16) 8 + 4096 < s.sp.toNat - 128 := by rw [hgS]; omega
    have hok := (hrdy.1 (by omega)).1
    janus_eval_nat h_ut : u8T
    rw [h_ut] at hdt hdtd hdesc hok
    janus_data hd [hw]
    have hu3 : S.mem.accessible 834336 16 false = true := by
      rw [hfr.accessible]
      exact Memory.accessible_sub s.mem (show s.mem.accessible 834336 256 false = true by janus_assumption) (Or.inl rfl) (by omega) (by omega)
    have hdescS : S.mem.readLE 834336 8 = 1 ∧ S.mem.readLE 834344 8 = 0 := by
      rcases hdesc with hdto | hR
      · have hOutU : ∀ a n, 834336 ≤ a → a + n ≤ 834336 + 16 →
            Outside a n (R.rt ++ [(s.sp.toNat - 4232, s.sp.toNat + 40), (dp, dp + cap0)]) := by
          intro a n h1 h2
          simp only [outside_append, outside_cons, outside_nil, and_true]
          unfold Apart at hdt hdtd
          refine ⟨Outside.of_sub hdto (by omega) (by omega), ?_, ?_⟩ <;> omega
        refine ⟨?_, ?_⟩
        · rw [hfr.readLE _ _ (hOutU _ _ (by omega) (by omega)), h_rodata _ _ (by decide)]; decide
        · rw [hfr.readLE _ _ (hOutU _ _ (by omega) (by omega)), h_rodata _ _ (by decide)]; decide
      · exact hR b L (s.regs 28).toNat S.mem hinv
    obtain ⟨hu1, hu2⟩ := hdescS
    clear hdesc
    obtain ⟨gp1, gp2, gp3, gp4⟩ := grow_pre_a64 len.toNat cc.toNat pp.toNat s.sp.toNat hlc hPb hdj hb'
    have pack := And.intro hrdy (And.intro hdj (And.intro hlc (And.intro hlle (And.intro hlge (And.intro hC (And.intro hPb (And.intro hcostK (And.intro hK (And.intro hbud (And.intro hwho (And.intro hzs (And.intro hmid (And.intro hpre (And.intro hzpd (And.intro hrd (True.intro))))))))))))))))
    replace pack := Nonempty.intro pack
    clear hrdy hdj hlc hlle hlge hC hPb hcostK hK hbud hwho hzs hmid hpre hzpd hrd
    janus_run [hu1, hu2] until [Extracted.entry + 0xb0] calls [hg]
    rename_i r0 r1 r2 jk fl vr M ex epm hfr' hpost hlf hfresh hapart hinv2
    obtain ⟨hr1, hr2, hin, hlim, hacc2, hcopy, hz1, hz2⟩ := hpost
    obtain ⟨pack⟩ := pack
    obtain ⟨hrdy, hdj, hlc, hlle, hlge, hC, hPb, hcostK, hK, hbud, hwho, hzs, hmid, hpre, hzpd, hrd, -⟩ := pack
    have hle := le_growCap 1 true (len.toNat + 8) cc.toNat (by omega)
    have hst : M.accessible (r0.toNat + len.toNat) 8 true = true :=
      Memory.accessible_sub M hacc2 (Or.inr rfl) (by omega) (by rw [Nat.mul_one]; omega)
    have hin16 : InRanges (s.sp.toNat - 24) 8 (R.rt ++ [(s.sp.toNat - 4232, s.sp.toNat + 40), (dp, dp + cap0)]) :=
      ⟨(s.sp.toNat - 4232, s.sp.toNat + 40), by simp, by omega, by omega⟩
    have hsM : MemFrame s.mem M (R.rt ++ [(s.sp.toNat - 4232, s.sp.toNat + 40), (dp, dp + cap0)]) :=
      MemFrame.trans (hfr.writeLE_inRanges (S.mem.readLE (z.toNat + 8) 8) hin16) hfr' (fun a n h => ⟨h, by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
        obtain ⟨h1, h2, h3⟩ := h
        refine ⟨h1, ?_, ?_⟩ <;> omega⟩)
    janus_data hd [hw, hst]
    janus_run until [Extracted.entry + 0xbc]
    have hr2pos : 0 < r2.toNat := by omega
    simp only [Nat.mul_one, Nat.add_sub_cancel] at hin hlim hacc2 hcopy
    rw [if_neg (by omega)] at hfresh hinv2
    have e1 : r1.toNat - 8 = len.toNat := by omega
    have hr1v : r1 = len + 8#64 := BitVec.eq_of_toNat_eq (by rw [hr1, hlen8])
    have hr2K : r2.toNat ≤ Kc len0 := by
      rw [hr2]; unfold growCap; simp only [Nat.mul_one, Nat.div_one]; exact hcostK
    have hK44 : Kc len0 < 2 ^ 44 := by unfold Kc; omega
    obtain ⟨rr, hrr, hrr1, hrr2⟩ := hin
    have hdo := MemFrame.outside_mem hout hrr
    have hinL' : InRanges (r0.toNat + len.toNat) 8 (L ++ [(r0.toNat, r0.toNat + r2.toNat)]) :=
      ⟨(r0.toNat, r0.toNat + r2.toNat), List.mem_append_right _ (by simp), by omega, by omega⟩
    have hinR : InRanges r0.toNat r2.toNat (L ++ [(r0.toNat, r0.toNat + r2.toNat)]) :=
      ⟨(r0.toNat, r0.toNat + r2.toNat), List.mem_append_right _ (by simp), Nat.le_refl _, Nat.le_refl _⟩
    have hdw : ∀ a, s.sp.toNat - 4232 ≤ a → a + 8 ≤ s.sp.toNat + 40 →
        a + 8 ≤ r0.toNat + len.toNat ∨ r0.toNat + len.toNat + 8 ≤ a := by intro a h1 h2; omega
    have hMr : ∀ a n, Outside a n R.rt →
        (a + n ≤ s.sp.toNat - 128 - 4096 ∨ (s.sp.toNat - 128 - 8 ≤ a ∧ a + n ≤ s.sp.toNat - 128 + 8) ∨
          s.sp.toNat - 128 + 8 + 40 ≤ a) →
        M.readLE a n = (S.mem.writeLE (s.sp.toNat - 24) 8 (S.mem.readLE (z.toNat + 8) 8)).readLE a n := fun a n ho hh =>
      hfr'.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        refine ⟨ho, ?_, ?_⟩ <;> omega)
    have hzp2 : Apart z.toNat 32 r0.toNat r2.toNat := by
      rcases hzL with ⟨r, hr, h1, h2⟩ | h
      · have := hfresh (r0.toNat, r0.toNat + r2.toNat) (by simp) r hr
        simp only [Nat.add_sub_cancel_left] at this
        unfold Apart at this ⊢; omega
      · have := MemFrame.outside_mem h hrr
        unfold Apart; omega
    refine hcont _ r0 r2 (b - roundupsize (nextslicecap (len.toNat + 8) cc.toNat) true)
      (L ++ [(r0.toNat, r0.toNat + r2.toNat)]) (by first | rfl | decide) ?_ (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [setReg, hrd3]
    · simp [setReg]
    · simp [setReg]
    · simp [setReg, hr1v]
    · simp [setReg, callRegs, h18]
    · simp [setReg, callRegs, h28]
    · simp [setReg, callRegs, h29]
    · dsimp only; rw [e1, Memory.readLE_writeLE_of_disjoint _ _ (hdw _ (by omega) (by omega)),
        hMr _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact hrd1
    · dsimp only; rw [e1, Memory.readLE_writeLE_of_disjoint _ _ (hdw _ (by omega) (by omega)),
        hMr _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact hrd2
    · dsimp only; rw [e1, Memory.readLE_writeLE_of_disjoint _ _ (hdw _ (by omega) (by omega)),
        hMr _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact hrd3
    · dsimp only; rw [Memory.accessible_writeLE, hfr'.accessible, Memory.accessible_writeLE]; exact hw
    · dsimp only; rw [e1]
      have hin16 : InRanges (s.sp.toNat - 24) 8 (R.rt ++ [(s.sp.toNat - 4232, s.sp.toNat + 40), (dp, dp + cap0)]) :=
        ⟨(s.sp.toNat - 4232, s.sp.toNat + 40), by simp, by omega, by omega⟩
      have hF1 := hfr.writeLE_inRanges (S.mem.readLE (z.toNat + 8) 8) hin16
      have hF2 := MemFrame.trans hF1 hfr' (fun a n h => ⟨h, by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
        obtain ⟨h1, h2, h3⟩ := h
        refine ⟨h1, ?_, ?_⟩ <;> omega⟩)
      exact hF2.writeLE_inRanges _ ⟨rr, List.mem_append_left _ hrr, by omega, by omega⟩
    · intro hng'
      obtain ⟨h1', h2', -⟩ := hng hng'
      omega
    · intro i hi; dsimp only; rw [e1]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hzp2; omega)]
      rcases hzL with ⟨r, hr, h1, h2⟩ | h
      · rw [hlf.readLE _ _ ⟨r, hr, by omega, by omega⟩ (by simp),
          Memory.readLE_writeLE_of_disjoint _ _ (by unfold Janus.Spec.Disjoint at hzd; omega)]
        exact hzs i hi
      · rw [hMr _ _ (Outside.of_sub h (by omega) (by omega)) (by unfold Janus.Spec.Disjoint at hzd; omega),
          Memory.readLE_writeLE_of_disjoint _ _ (by unfold Janus.Spec.Disjoint at hzd; omega)]
        exact hzs i hi
    · dsimp only; rw [e1, view_writeLE_live hinL']; exact hinv2
    · intro r hr
      rcases List.mem_append.1 hr with h | h
      · exact hLs r h
      · simp only [List.mem_singleton] at h; subst h
        simp only [outside_cons, outside_nil, and_true]; omega
    · rcases hzL with ⟨r, hr, h1, h2⟩ | h
      · exact Or.inl ⟨r, List.mem_append_left _ hr, h1, h2⟩
      · exact Or.inr h
    · exact hzp2
    · rw [hlen8]; omega
    · rw [hlen8]; omega
    · rw [hlen8]; omega
    · omega
    · omega
    · unfold Apart; omega
    · intro _; dsimp only; rw [Memory.accessible_writeLE]; exact ⟨hacc2, Or.inl hinR⟩
    · intro _ h0'; dsimp only; rw [Memory.accessible_writeLE, hlen8]
      exact Memory.accessible_sub M hacc2 (Or.inl rfl) (Nat.le_refl _) (by omega)
    · rw [Nat.succ_mul] at hbud; omega
    · rw [hlen8, hr2]; exact (hrdy.1 (by omega)).2
    · exact Or.inr ⟨rr, hrr, hrr1, hrr2⟩
    · intro i hi; dsimp only
      rw [Memory.bytes_writeLE_outside _ (Or.inl (by omega)), hcopy i (by omega),
        Memory.bytes_writeLE_outside _ (by unfold Apart at hdj; omega)]
      exact hpre i hi
    · dsimp only
      have hmid' : M.readLE (r0.toNat + len0) (len.toNat - len0) = S.mem.readLE (pp.toNat + len0) (len.toNat - len0) := by
        apply readLE_bytes_shift; intro i hi
        rw [show r0.toNat + len0 + i = r0.toNat + (len0 + i) by omega, hcopy (len0 + i) (by omega),
          Memory.bytes_writeLE_outside _ (by unfold Apart at hdj; omega),
          show pp.toNat + (len0 + i) = pp.toNat + len0 + i by omega]
      have h1 : len.toNat + 8 - len0 = (len.toNat - len0) + 8 := by omega
      have h2 : r0.toNat + len.toNat = r0.toNat + len0 + (len.toNat - len0) := by omega
      rw [e1, hlen8, h1, h2]
      exact mid_step M s.mem (r0.toNat + len0) (len.toNat - len0) z.toNat _ (hmid'.trans hmid)
        (by rw [Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _), show z.toNat + (len.toNat - len0) = z.toNat + 8 by omega]; exact hz8)

end Fv256.Arm64.MarshalSSZAppendG
