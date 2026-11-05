import Fv256.Amd64.IntoBigFinF
import Fv256.Amd64.IntoBigClose

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Amd64.IntoBig

/-- The pc after the normalization loop of the allocating path: `cmp $4,%rcx` (`IntoBig+0x10f`). -/
abbrev pcTail : Nat := Extracted.entry + 0x10f

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- The allocating path after the copy and the normalization: the stores and the barrier. -/
theorem slowTail (impl : List Amd64.Segment) (R : RtInv) (b b1 : Nat) (z bp : BitVec 64) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret) (s : State)
    (hwb2 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hpre : Pre R b z bp s) (hz0 : z.toNat ≠ 0)
    (S2 : State) (w2 : Memory)
    (hsp : S2.regs 4 = s.regs 4 - 24#64) (h28 : S2.regs 14 = s.regs 14) (h29 : S2.regs 5 = s.regs 4 - 8#64)
    (hx15 : S2.xmm 15 = s.xmm 15) (h_rd1 : S2.mem.readLE (s.regs 4).toNat 8 = ret)
    (h_rd2 : S2.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (h_rd3 : S2.mem.readLE ((s.regs 4).toNat + 8) 8 = z.toNat) (h_rd4 : S2.mem.readLE ((s.regs 4).toNat + 16) 8 = bp.toNat)
    (hfr2 : MemFrame s.mem S2.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24), (bp.toNat, bp.toNat + 8)]))
    (hpc : S2.rip = BitVec.ofNat 64 pcTail)
    (A' P len : Nat) (hA0 : (S2.regs 0).toNat = A') (hA1 : (S2.regs 1).toNat = len)
    (hlen : len ≤ 4) (h_rdP : S2.mem.readLE bp.toNat 8 = P)
    (hPa : s.mem.accessible P 32 true = true) (hP48 : P + 32 ≤ 2 ^ 48)
    (hAacc : s.mem.accessible A' 32 true = true) (hA48 : A' + 32 ≤ 2 ^ 48)
    (hPd : Apart ((s.regs 4).toNat - 4128) 4152 P 32) (hAd : Apart ((s.regs 4).toNat - 4128) 4152 A' 32)
    (hgP : Apart P 32 ((s.regs 14).toNat + 16) 8) (hgA : Apart A' 32 ((s.regs 14).toNat + 16) 8)
    (hAP : Apart A' 32 P 32) (hbP : Apart bp.toNat 8 P 32)
    (hword : ∀ i, i < 4 → S2.mem.readLE (A' + 8 * i) 8 = s.mem.readLE (z.toNat + 8 * i) 8)
    (hnorm : len = 0 ∨ s.mem.readLE (z.toNat + 8 * (len - 1)) 8 ≠ 0)
    (hzero : ∀ i, len ≤ i → i < 4 → s.mem.readLE (z.toNat + 8 * i) 8 = 0)
    (L0 : List (Nat × Nat)) (hPrt : (L0 = [] ∧ Outside P 32 R.rt) ∨ (L0 = [(P, P + 32)] ∧ InRanges P 32 R.rt))
    (hinv : R.inv b1 (L0 ++ [(A', A' + 32)]) (s.regs 14).toNat (view R.rt (L0 ++ [(A', A' + 32)]) S2.mem)) :
    Reaches ((Extracted.program.link impl).withExit ret) S2
      (IsReturn fun s' => ABIReturn s s' ∧ BigOut s'.mem bp.toNat P (val256 s.mem z.toNat) ∧
        MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24), (bp.toNat, bp.toNat + 8), (P, P + 32)])) := by
  have h0 : S2.regs 0 = BitVec.ofNat 64 A' := by rw [← hA0]; simp
  have h1 : S2.regs 1 = BitVec.ofNat 64 len := by rw [← hA1]; simp
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hflag, hty1, hty2, hok1, hok2, hok3, hok4,
    hinv0, hbud, ⟨hbpa, hbpb⟩, hbpo, hbpd, hz⟩ := hpre
  have hret48 := hret.user
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset, Janus.Amd64.GoABI.stackguard0] at hg hb' ha hw hal hout hga hgr
  have hspn : (S2.regs 4).toNat = (s.regs 4).toNat - 24 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  unfold Apart at hPd hAd hga
  simp only [Janus.Spec.Disjoint] at hbpd
  have hfacts : Hidden (Apart bp.toNat 8 P 32 ∧
      (∀ i, i < 4 → S2.mem.readLE (A' + 8 * i) 8 = s.mem.readLE (z.toNat + 8 * i) 8) ∧
      (len = 0 ∨ s.mem.readLE (z.toNat + 8 * (len - 1)) 8 ≠ 0) ∧
      (∀ i, len ≤ i → i < 4 → s.mem.readLE (z.toNat + 8 * i) 8 = 0)) := ⟨hbP, hword, hnorm, hzero⟩
  clear hbP hword hnorm hzero
  janus64_data hd [hw, hbpb, hPa]
  janus_eval_nat h_f : flagAddr
  rw [h_f] at hflag
  rcases hPrt with ⟨hL, hPo⟩ | ⟨hL, hPi⟩
  · subst hL
    have hPo16 : Outside (P + 16) 8 R.rt := Outside.of_sub hPo (by omega) (by omega)
    have hPo24 : Outside (P + 24) 8 R.rt := Outside.of_sub hPo (by omega) (by omega)
    janus64_run calls [hwb2]
    all_goals (try rw [← Spec.val256_limbs s.mem z.toNat])
    all_goals (unfold Hidden at hfacts)
    all_goals (obtain ⟨hbP, hword, hnorm, hzero⟩ := hfacts)
    all_goals first
      | (set_option maxHeartbeats 300000 in exact ⟨tail0_bigout (sp := (s.regs 4).toNat) hfr2 h_rdP hPa hP48 hAacc hA48 hbP hAP hlen hword hnorm hzero,
          tail0_frame hfr2⟩)
      | (set_option maxHeartbeats 600000 in exact ⟨tail1_bigout (sp := (s.regs 4).toNat) hfr2 h_rdP hPa hP48 hAacc hA48 hbP hAP hlen hword hnorm hzero hbpo hbpd hb'
            (unpush1 (show MemFrame _ _ _ by janus_assumption) (by omega)) (live_unpush (show LiveFrame _ _ _ _ by janus_assumption) (by intro r hr; simp at hr; subst hr; simp; omega)) ⟨(A', A' + 32), by simp, Nat.le_refl _, Nat.le_refl _⟩ (show InRanges (BitVec.toNat _) 16 R.rt by janus_assumption)
            (read_wbp (show MemFrame _ _ _ by janus_assumption) hPo16 (by omega) (by omega)) (read_wbp (show MemFrame _ _ _ by janus_assumption) hPo24 (by omega) (by omega)) (Or.symm (show Apart (BitVec.toNat _) 16 A' 32 by janus_assumption)) (show Apart P 32 (BitVec.toNat _) 16 by janus_assumption),
          tail1_frame hfr2 hb' (unpush1 (show MemFrame _ _ _ by janus_assumption) (by omega)) (show InRanges (BitVec.toNat _) 16 R.rt by janus_assumption)⟩)
  · subst hL
    have hPi16 : InRanges (P + 16) 8 ([(P, P + 32)] ++ [(A', A' + 32)]) :=
      ⟨(P, P + 32), by simp, by omega, by omega⟩
    have hPi24 : InRanges (P + 24) 8 ([(P, P + 32)] ++ [(A', A' + 32)]) :=
      ⟨(P, P + 32), by simp, by omega, by omega⟩
    janus64_run calls [hwb2]
    all_goals (try rw [← Spec.val256_limbs s.mem z.toNat])
    all_goals (unfold Hidden at hfacts)
    all_goals (obtain ⟨hbP, hword, hnorm, hzero⟩ := hfacts)
    all_goals first
      | (set_option maxHeartbeats 300000 in exact ⟨tail0_bigout (sp := (s.regs 4).toNat) hfr2 h_rdP hPa hP48 hAacc hA48 hbP hAP hlen hword hnorm hzero,
          tail0_frame hfr2⟩)
      | (obtain ⟨hAw, hPw⟩ : Apart (BitVec.toNat _) 16 A' 32 ∧ Apart P 32 (BitVec.toNat _) 16 :=
           ⟨((show Apart (BitVec.toNat _) 16 P 32 ∧ Apart (BitVec.toNat _) 16 A' 32 by janus_assumption)).2,
            Or.symm ((show Apart (BitVec.toNat _) 16 P 32 ∧ Apart (BitVec.toNat _) 16 A' 32 by janus_assumption)).1⟩
         have hLv : LiveFrame (M1 S2.mem P len) _ [(P, P + 32), (A', A' + 32)] [] :=
           live_unpush (show LiveFrame _ _ _ _ by janus_assumption) (by intro r hr; simp at hr; rcases hr with rfl | rfl <;> simp <;> omega)
         set_option maxHeartbeats 600000 in
         exact ⟨tail1_bigout (s := s.mem) (W := S2.mem) (sp := (s.regs 4).toNat) (bp := bp.toNat) (z := z.toNat) (P := P) (A' := A') (len := len) (rt := R.rt)
              (L1 := [(P, P + 32), (A', A' + 32)]) hfr2 h_rdP hPa hP48 hAacc hA48 hbP hAP hlen hword hnorm hzero hbpo hbpd hb'
              (unpush1 (show MemFrame _ _ _ by janus_assumption) (by omega)) hLv ⟨(A', A' + 32), by simp, Nat.le_refl _, Nat.le_refl _⟩ (show InRanges (BitVec.toNat _) 16 R.rt by janus_assumption)
              (hLv.readLE (P + 16) 8 ⟨(P, P + 32), by simp, by omega, by omega⟩ trivial)
              (hLv.readLE (P + 24) 8 ⟨(P, P + 32), by simp, by omega, by omega⟩ trivial) (Or.symm hAw) hPw,
            tail1_frame (s := s.mem) (W := S2.mem) (sp := (s.regs 4).toNat) (bp := bp.toNat) (P := P) (A' := A') (len := len) (rt := R.rt)
              hfr2 hb' (unpush1 (show MemFrame _ _ _ by janus_assumption) (by omega)) (show InRanges (BitVec.toNat _) 16 R.rt by janus_assumption)⟩)

end Fv256.Amd64.IntoBig
