import Fv256.Amd64.MsaBlk0

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Arm64 (Memory)

namespace Fv256.Amd64.Msa

open Fv256.Msa

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem blk1 (impl : List Amd64.Segment) (R : RtInv) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret)
    (hg : RtLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive)
    (s S : State) (z : BitVec 64) (dp len0 cap0 b b0 : Nat) (len pp cc : BitVec 64) (L L0 : List (Nat × Nat))
    (Q : Amd64.Outcome → Prop)
    (hsg : StackGuardOK s 4208) (hal : (s.regs 4).toNat % 8 = 0)
    (hb' : 4208 ≤ (s.regs 4).toNat) (ha : (s.regs 4).toNat + 24 ≤ 2 ^ 48)
    (hga : Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4208) 4232)
    (hgr : Outside ((s.regs 14).toNat + 16) 8 R.rt)
    (hgd : Apart ((s.regs 14).toNat + 16) 8 dp cap0)
    (hzp : s.mem.accessible z.toNat 32 false = true) (hz48 : z.toNat + 32 ≤ 2 ^ 48)
    (hzd : Apart z.toNat 32 ((s.regs 4).toNat - 4208) 4232)
    (hout : Outside ((s.regs 4).toNat - 4208) 4232 R.rt)
    (hdt : Apart u8T 16 ((s.regs 4).toNat - 4208) 4232) (hdtd : Apart u8T 16 dp cap0)
    (hd : Extracted.program.DataLoaded s.mem) (hdesc : DescOK R u8T)
    (hl0 : len.toNat = len0 + 8) (hk : len.toNat + 8 ≤ len0 + 32) (hl0b : len0 < 2 ^ 40) (hs15 : s.xmm 15 = 0)
    (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x63))
    (m : Nat) (hI : BI R ga u8T s S z ret dp len0 cap0 b0 L0 len pp cc b L (m + 1))
    (hcont : ∀ (S' : State) (pp' cc' : BitVec 64) (b' : Nat) (L' : List (Nat × Nat)),
      S'.rip = BitVec.ofNat 64 (Extracted.entry + 0xa7) →
      BI R ga u8T s S' z ret dp len0 cap0 b0 L0 (len + 8#64) pp' cc' b' L' m → b - Kc len0 ≤ b' →
      Reaches ((Extracted.program.link impl).withExit ret) S' Q) :
    Reaches ((Extracted.program.link impl).withExit ret) S Q := by
  obtain ⟨hsp, h0, h3, h2, h7, h5, h14, hx15, h_rd1, h_rd2, h_rd3, hw, hfr, hng, hzs, hinv, hLs, hzL, hzpd, hlge, hlle, hlc,
    hC, hPb, hdj, hroom, hgrow, hbud, hrdy, hwho, hpre, hmid⟩ := hI
  have hgl := hsg.load
  have hgb := hsg.below
  have hnw := hsg.noWrap
  have hgrd := hsg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset, Janus.Amd64.GoABI.stackguard0] at hgl hgb hnw hgrd hb' ha hal hga hgr hgd hw hzd hout hdt hdtd hfr hng h_rd1 h_rd2 h_rd3 hdj hinv hLs hsp h5 h14
  have hlen8 : (len + 8#64).toNat = len.toNat + 8 := by
    rw [BitVec.toNat_add]; simp; omega
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 104 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hr2' : (S.regs 2).toNat = len.toNat + 8 := by rw [h2, hlen8]
  have hz8 : S.mem.readLE (z.toNat + 8) 8 = s.mem.readLE (z.toNat + 8) 8 := hzs (1) (by omega)
  have hzS : S.mem.accessible z.toNat 32 false = true := by
    rw [hfr.accessible]; exact hzp
  have hfrH : Hidden (MemFrame s.mem S.mem (R.rt ++ [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24), (dp + len0, dp + cap0)])) := hfr
  clear hfr
  have hws : s.mem.accessible ((s.regs 4).toNat - 4208) (4208 + 24) true = true := by
    rw [← (show MemFrame s.mem S.mem _ from hfrH).accessible]; exact hw
  by_cases hl : len.toNat + 8 ≤ cc.toNat
  · obtain ⟨hacc, hdest⟩ := hroom hl
    have hap : Apart (pp.toNat + len.toNat) 8 ((s.regs 4).toNat - 4208) 4232 := by
      unfold Apart at hdj ⊢; omega
    have hacc9 : S.mem.accessible (len.toNat + 8 + pp.toNat - 8) 8 true = true :=
      Memory.accessible_sub S.mem hacc (Or.inr rfl) (by omega) (by omega)
    have hacc8 : S.mem.accessible (pp.toNat + len.toNat) 8 true = true :=
      Memory.accessible_sub S.mem hacc (Or.inr rfl) (by omega) (by omega)
    have hacs : s.mem.accessible pp.toNat cc.toNat true = true := by
      rw [← (show MemFrame s.mem S.mem _ from hfrH).accessible]; exact hacc
    janus64_data hd [hws, hacs]
    have hin : InRanges (pp.toNat + len.toNat) 8 (R.rt ++ [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24), (dp + len0, dp + cap0)]) := by
      rcases hwho with ⟨h1, h2⟩ | ⟨r, hr, h1, h2⟩
      · exact ⟨(dp + len0, dp + cap0), by simp, by omega, by omega⟩
      · exact ⟨r, by simp [hr], by omega, by omega⟩
    janus64_run until [Extracted.entry + 0xa7]
    have e : len.toNat + 8 + pp.toNat - 8 = pp.toNat + len.toNat := by omega
    rw [e]
    refine hcont _ pp cc b L (by first | rfl | decide) ?_ (by omega)
    have hfrU := show MemFrame s.mem S.mem _ from hfrH
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF, hsp]
    · simp [setRegF, h0]
    · simp [setRegF, h3]
    · simp [setRegF]; bv_omega
    · simp [setRegF, h7]
    · simp [setRegF, h5]
    · simp [setRegF, h14]
    · simp [hx15]
    · dsimp only; rw [Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hap; omega)]; exact h_rd1
    · dsimp only; rw [Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hap; omega)]; exact h_rd2
    · dsimp only; rw [Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hap; omega)]; exact h_rd3
    · dsimp only; rw [Memory.accessible_writeLE]; exact hw
    · exact hfrU.writeLE_inRanges _ hin
    · intro hng'
      obtain ⟨h1, h2, h3, h4, h3'⟩ := hng hng'
      refine ⟨h1, h2, h3, h4, ?_⟩
      have h3w := h3'.mono (rs' := [(dp + len0, dp + len.toNat + 8), ((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24)]) (by
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
        (by rw [Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _), show z.toNat + (len.toNat - len0) = z.toNat + 8 by omega])
  · have hcostK := cost_le len0 len.toNat cc.toNat (by omega) (by omega)
    have hK : Kc len0 ≤ b := by rw [Nat.succ_mul] at hbud; omega
    obtain ⟨hrd⟩ := (⟨hgrow (by omega)⟩ : Nonempty _)
    have hok := (hrdy.1 (by omega)).1
    janus_eval_nat h_ut : u8T
    rw [h_ut] at hdt hdtd hok hdesc
    have hw16 : S.mem.accessible ((s.regs 4).toNat - 24) 8 true = true :=
      Memory.accessible_sub S.mem hw (Or.inr rfl) (by omega) (by omega)
    janus64_data hd [hws]
    have hfrU := show MemFrame s.mem S.mem _ from hfrH
    have hu3 : S.mem.accessible 5008256 16 false = true := by
      rw [hfrU.accessible]
      exact Memory.accessible_sub s.mem (show s.mem.accessible 5008256 256 false = true by janus_assumption) (Or.inl rfl) (by omega) (by omega)
    have hdescS : S.mem.readLE 5008256 8 = 1 ∧ S.mem.readLE 5008264 8 = 0 := by
      rcases hdesc with hdto | hR
      · have hOutU : ∀ a n, 5008256 ≤ a → a + n ≤ 5008256 + 16 →
            Outside a n (R.rt ++ [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24), (dp + len0, dp + cap0)]) := by
          intro a n h1 h2
          simp only [outside_append, outside_cons, outside_nil, and_true]
          unfold Apart at hdt hdtd
          refine ⟨Outside.of_sub hdto (by omega) (by omega), ?_, ?_⟩ <;> omega
        refine ⟨?_, ?_⟩
        · rw [hfrU.readLE _ _ (hOutU _ _ (by omega) (by omega)), h_rodata _ _ (by decide)]; decide
        · rw [hfrU.readLE _ _ (hOutU _ _ (by omega) (by omega)), h_rodata _ _ (by decide)]; decide
      · exact hR b L (s.regs 14).toNat S.mem hinv
    obtain ⟨hu1, hu2⟩ := hdescS
    have hgS : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
      hfrU.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        refine ⟨hgr, ?_, ?_⟩ <;> (unfold Apart at hga hgd; omega))
    have hgacc : S.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by
      rw [hfrU.accessible]; exact hgrd
    clear hfrU
    have hgC : ((S.mem.writeLE ((s.regs 4).toNat - 24) 8 (s.mem.readLE (z.toNat + 8) 8)).writeLE ((s.regs 4).toNat - 112) 8 4926763).readLE
        ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hga; omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hga; omega)]
      exact hgS
    have hgA1 : (s.regs 14).toNat + 16 + 8 ≤ (s.regs 4).toNat - 112 - 4096 ∨ (s.regs 4).toNat - 112 ≤ (s.regs 14).toNat + 16 := by
      unfold Apart at hga; omega
    have hgA2 : (s.regs 14).toNat + 16 ≤ (s.regs 4).toNat - 112 ∨ (s.regs 4).toNat - 112 + 32 ≤ (s.regs 14).toNat := by
      unfold Apart at hga; omega
    obtain ⟨gp0, gp1, gp2, gp3, gp4, gp5, gp6⟩ := grow_pre len.toNat cc.toNat pp.toNat len0 b (s.regs 4).toNat hlc hk hl0b hPb hdj hb' hcostK hK _ hgb
    have pack := And.intro hga (And.intro hgd (And.intro hzd (And.intro hdt (And.intro hdtd (And.intro hdj (And.intro hlc (And.intro hlle (And.intro hlge (And.intro hC (And.intro hPb (And.intro hcostK (And.intro hK (And.intro hbud (And.intro hl0b (And.intro hrdy (And.intro hzs (And.intro hmid (And.intro hpre (And.intro hzpd (And.intro hwho (True.intro)))))))))))))))))))))
    replace pack := Nonempty.intro pack
    clear hga hgd hzd hdt hdtd hdj hlc hlle hlge hC hPb hcostK hK hbud hl0b hrdy hzs hmid hpre hzpd hwho
    janus64_run [hu1, hu2, hgC] until [Extracted.entry + 0x8b] calls [hg]
    rename_i r0 r1 r2 jk fl xm xm2 M ex epm hfr' hpost hlf hfresh hapart hinv2
    obtain ⟨hr1, hr2, hin, hlim, hacc2, hcopy, hz1, hz2⟩ := hpost
    have hle := le_growCap 1 true (len.toNat + 8) cc.toNat (by omega)
    have hst : M.accessible (r0.toNat + len.toNat) 8 true = true :=
      Memory.accessible_sub M hacc2 (Or.inr rfl) (by omega) (by rw [Nat.mul_one]; omega)
    have hfrU := show MemFrame s.mem S.mem _ from hfrH
    have hin16 : InRanges ((s.regs 4).toNat - 24) 8 (R.rt ++ [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24), (dp + len0, dp + cap0)]) :=
      ⟨((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24), by simp, by omega, by omega⟩
    have hin112 : InRanges ((s.regs 4).toNat - 112) 8 (R.rt ++ [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24), (dp + len0, dp + cap0)]) :=
      ⟨((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24), by simp, by omega, by omega⟩
    have hsM : MemFrame s.mem M (R.rt ++ [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24), (dp + len0, dp + cap0)]) :=
      MemFrame.trans ((hfrU.writeLE_inRanges _ hin16).writeLE_inRanges _ hin112) hfr'
        (fun a n h => ⟨h, by
          simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
          obtain ⟨h1, h2, h3⟩ := h
          refine ⟨h1, ?_, ?_⟩ <;> omega⟩)
    have hsts : s.mem.accessible (r0.toNat + len.toNat) 8 true = true := by
      rw [← hsM.accessible]; exact hst
    have hMr : ∀ a n, Outside a n R.rt →
        (a + n ≤ (s.regs 4).toNat - 112 - 4096 ∨ ((s.regs 4).toNat - 112 ≤ a ∧ a + n ≤ (s.regs 4).toNat - 112 + 8) ∨
          (s.regs 4).toNat - 112 + 8 + 40 ≤ a) →
        M.readLE a n = ((S.mem.writeLE ((s.regs 4).toNat - 24) 8 (s.mem.readLE (z.toNat + 8) 8)).writeLE ((s.regs 4).toNat - 112) 8 4926763).readLE a n :=
      fun a n ho hh => hfr'.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        refine ⟨ho, ?_, ?_⟩ <;> omega)
    have hM16 : M.readLE ((s.regs 4).toNat - 24) 8 = s.mem.readLE (z.toNat + 8) 8 := by
      rw [hMr _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _)
    have hM70 : M.readLE ((s.regs 4).toNat + 8) 8 = z.toNat := by
      rw [hMr _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact h_rd3
    have hMa16 : M.accessible ((s.regs 4).toNat - 24) 8 false = true := by
      rw [hsM.accessible, ← hfrU.accessible]
      exact Memory.accessible_sub S.mem hw (Or.inl rfl) (by omega) (by omega)
    have hMa70 : M.accessible ((s.regs 4).toNat + 8) 8 false = true := by
      rw [hsM.accessible, ← hfrU.accessible]
      exact Memory.accessible_sub S.mem hw (Or.inl rfl) (by omega) (by omega)
    have hMa8 : M.accessible ((s.regs 4).toNat - 8) 8 false = true := by
      rw [hsM.accessible, ← hfrU.accessible]
      exact Memory.accessible_sub S.mem hw (Or.inl rfl) (by omega) (by omega)
    have hMa0 : M.accessible (s.regs 4).toNat 8 false = true := by
      rw [hsM.accessible, ← hfrU.accessible]
      exact Memory.accessible_sub S.mem hw (Or.inl rfl) (by omega) (by omega)
    have hM8 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
      rw [hMr _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact h_rd2
    clear hfrU
    replace hfr' := show Hidden _ from hfr'
    replace hsM := show Hidden _ from hsM
    janus64_data hd [hws, hsts]
    janus64_run [hM16, hM70] until [Extracted.entry + 0xa7]
    obtain ⟨pack⟩ := pack
    obtain ⟨hga, hgd, hzd, hdt, hdtd, hdj, hlc, hlle, hlge, hC, hPb, hcostK, hK, hbud, hl0b, hrdy, hzs, hmid, hpre, hzpd, hwho, -⟩ := pack
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
    have hW : r1.toNat + r0.toNat - 8 = r0.toNat + len.toNat := by omega
    rw [hW]
    have hinL' : InRanges (r0.toNat + len.toNat) 8 (L ++ [(r0.toNat, r0.toNat + r2.toNat)]) :=
      ⟨(r0.toNat, r0.toNat + r2.toNat), List.mem_append_right _ (by simp), by omega, by omega⟩
    have hinR : InRanges r0.toNat r2.toNat (L ++ [(r0.toNat, r0.toNat + r2.toNat)]) :=
      ⟨(r0.toNat, r0.toNat + r2.toNat), List.mem_append_right _ (by simp), Nat.le_refl _, Nat.le_refl _⟩
    have hzp2 : Apart z.toNat 32 r0.toNat r2.toNat := by
      rcases hzL with ⟨r, hr, h1, h2⟩ | h
      · have := hfresh (r0.toNat, r0.toNat + r2.toNat) (by simp) r hr
        simp only [Nat.add_sub_cancel_left] at this
        unfold Apart at this ⊢; omega
      · have := MemFrame.outside_mem h hrr
        unfold Apart; omega
    have hMS : ∀ a n, Outside a n R.rt → (a + n ≤ (s.regs 4).toNat - 4208 ∨ ((s.regs 4).toNat - 64 ≤ a ∧ a + n ≤ (s.regs 4).toNat - 24) ∨ (s.regs 4).toNat - 8 ≤ a) →
        M.readLE a n = S.mem.readLE a n := fun a n ho hh => by
      rw [hMr a n ho (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    have hdw : ∀ a, (s.regs 4).toNat - 4208 ≤ a → a + 8 ≤ (s.regs 4).toNat + 24 →
        a + 8 ≤ r0.toNat + len.toNat ∨ r0.toNat + len.toNat + 8 ≤ a := by intro a h1 h2; omega
    refine hcont _ r0 r2 (b - roundupsize (nextslicecap (len.toNat + 8) cc.toNat) true)
      (L ++ [(r0.toNat, r0.toNat + r2.toNat)]) (by first | rfl | decide) ?_ (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF, callRegs64_apply]; bv_omega
    · simp [setRegF, callRegs64_apply]
    · simp [setRegF, callRegs64_apply]
    · simp [setRegF, callRegs64_apply, hr1v]
    · simp [setRegF, callRegs64_apply]
    · simp [setRegF, callRegs64_apply, h5]
    · simp [setRegF, callRegs64_apply, h14]
    · simp [hs15]
    · dsimp only; rw [Memory.readLE_writeLE_of_disjoint _ _ (by have := hdw ((s.regs 4).toNat) (by omega) (by omega); omega), hMS _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega)]; exact h_rd1
    · dsimp only; rw [Memory.readLE_writeLE_of_disjoint _ _ (by have := hdw ((s.regs 4).toNat - 8) (by omega) (by omega); omega), hMS _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega)]; exact h_rd2
    · dsimp only; rw [Memory.readLE_writeLE_of_disjoint _ _ (by have := hdw ((s.regs 4).toNat + 8) (by omega) (by omega); omega), hMS _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega)]; exact h_rd3
    · dsimp only; rw [Memory.accessible_writeLE, (show MemFrame s.mem M _ from hsM).accessible]
      exact hws
    · dsimp only
      exact (show MemFrame s.mem M _ from hsM).writeLE_inRanges _ ⟨rr, List.mem_append_left _ hrr, by omega, by omega⟩
    · intro hng'
      obtain ⟨h1, h2, -⟩ := hng hng'
      omega
    · intro i hi; dsimp only
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hzp2; omega)]
      rcases hzL with ⟨r, hr, h1, h2⟩ | h
      · rw [hlf.readLE _ _ ⟨r, hr, by omega, by omega⟩ (by simp), Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hzd; omega),
          Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hzd; omega)]
        exact hzs i hi
      · rw [hMr _ _ (Outside.of_sub h (by omega) (by omega)) (by unfold Apart at hzd; omega),
          Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hzd; omega), Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hzd; omega)]
        exact hzs i hi
    · dsimp only; rw [view_writeLE_live hinL']; exact hinv2
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
    · rw [hlen8, hr2]; exact (hrdy.1 hbr).2
    · exact Or.inr ⟨rr, hrr, hrr1, hrr2⟩
    · intro i hi; dsimp only
      rw [Memory.bytes_writeLE_outside _ (Or.inl (by omega)), hcopy i (by omega),
        Memory.bytes_writeLE_outside _ (by unfold Apart at hdj; omega), Memory.bytes_writeLE_outside _ (by unfold Apart at hdj; omega)]
      exact hpre i hi
    · dsimp only
      have hmid' : M.readLE (r0.toNat + len0) (len.toNat - len0) = S.mem.readLE (pp.toNat + len0) (len.toNat - len0) := by
        apply readLE_bytes_shift; intro i hi
        rw [show r0.toNat + len0 + i = r0.toNat + (len0 + i) by omega, hcopy (len0 + i) (by omega),
          Memory.bytes_writeLE_outside _ (by unfold Apart at hdj; omega), Memory.bytes_writeLE_outside _ (by unfold Apart at hdj; omega),
          show pp.toNat + (len0 + i) = pp.toNat + len0 + i by omega]
      have h1 : len.toNat + 8 - len0 = (len.toNat - len0) + 8 := by omega
      have h2 : r0.toNat + len.toNat = r0.toNat + len0 + (len.toNat - len0) := by omega
      rw [hlen8, h1, h2]
      exact mid_step M s.mem (r0.toNat + len0) (len.toNat - len0) z.toNat _ (hmid'.trans hmid)
        (by rw [Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _), show z.toNat + (len.toNat - len0) = z.toNat + 8 by omega])

end Fv256.Amd64.Msa
