import Fv256.Arm64.TB.IntoBigFinF
import Fv256.Arm64.TB.IntoBigClose

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.IntoBig

/-- The pc after the normalization loop of the allocating path: `cmp x1, #4` (`IntoBig+0x108`). -/
abbrev pcTail : Nat := (Extracted.entry + 0x60) + 0x108

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- The allocating path after the copy and the normalization: the stores and the barrier. -/
theorem slowTail (impl : List Segment) (R : RtInv) (b b1 : Nat) (z bp : BitVec 64) (ret : Nat)
    (hret : RetAddr ((Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).IntoBig"]).link impl) ret) (s : State)
    (hwb2 : WbLiveContract ((Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).IntoBig"]).link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hpre : Pre R b z bp s) (hz0 : z.toNat ≠ 0)
    (S2 : State) (w2 : Memory)
    (hsp : S2.sp = s.sp - 48#64) (h28 : S2.regs 28 = s.regs 28) (h29 : S2.regs 29 = s.sp - 56#64)
    (h18 : S2.regs 18 = s.regs 18) (h_rd1 : S2.mem.readLE (s.sp.toNat - 48) 8 = ret)
    (h_rd2 : S2.mem.readLE (s.sp.toNat - 56) 8 = (s.regs 29).toNat)
    (h_rd3 : S2.mem.readLE (s.sp.toNat + 8) 8 = z.toNat) (h_rd4 : S2.mem.readLE (s.sp.toNat + 16) 8 = bp.toNat)
    (hfr2 : MemFrame s.mem S2.mem (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24), (bp.toNat, bp.toNat + 8)]))
    (hpc : S2.pc = BitVec.ofNat 64 pcTail)
    (A' P len : Nat) (hA0 : (S2.regs 0).toNat = A') (hA1 : (S2.regs 1).toNat = len)
    (hlen : len ≤ 4) (h_rdP : S2.mem.readLE bp.toNat 8 = P)
    (hPa : s.mem.accessible P 32 true = true) (hP48 : P + 32 ≤ 2 ^ 48)
    (hAacc : s.mem.accessible A' 32 true = true) (hA48 : A' + 32 ≤ 2 ^ 48)
    (hPd : Apart (s.sp.toNat - 4144) 4168 P 32) (hAd : Apart (s.sp.toNat - 4144) 4168 A' 32)
    (hgP : Apart P 32 ((s.regs 28).toNat + 16) 8) (hgA : Apart A' 32 ((s.regs 28).toNat + 16) 8)
    (hAP : Apart A' 32 P 32) (hbP : Apart bp.toNat 8 P 32)
    (hword : ∀ i, i < 4 → S2.mem.readLE (A' + 8 * i) 8 = s.mem.readLE (z.toNat + 8 * i) 8)
    (hnorm : len = 0 ∨ s.mem.readLE (z.toNat + 8 * (len - 1)) 8 ≠ 0)
    (hzero : ∀ i, len ≤ i → i < 4 → s.mem.readLE (z.toNat + 8 * i) 8 = 0)
    (L0 : List (Nat × Nat)) (hPrt : (L0 = [] ∧ Outside P 32 R.rt) ∨ (L0 = [(P, P + 32)] ∧ InRanges P 32 R.rt))
    (hinv : R.inv b1 (L0 ++ [(A', A' + 32)]) (s.regs 28).toNat (view R.rt (L0 ++ [(A', A' + 32)]) S2.mem)) :
    Reaches (((Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).IntoBig"]).link impl).withExit ret) S2
      (IsReturn fun s' => ABIReturn s s' ∧ BigOut s'.mem bp.toNat P (val256 s.mem z.toNat) ∧
        MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24), (bp.toNat, bp.toNat + 8), (P, P + 32)])) := by
  have h0 : S2.regs 0 = BitVec.ofNat 64 A' := by rw [← hA0]; simp
  have h1 : S2.regs 1 = BitVec.ofNat 64 len := by rw [← hA1]; simp
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hflag, hty1, hty2, hok1, hok2, hok3, hok4,
    hinv0, hbud, ⟨hbpa, hbpb⟩, hbpo, hbpd, hz⟩ := hpre
  have hret48 := hret.user
  have hret4 := hret.aligned
  have hspn : S2.sp.toNat = s.sp.toNat - 48 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  unfold Apart at hPd hAd hga
  simp only [Disjoint] at hbpd
  have hfacts : Hidden (Apart bp.toNat 8 P 32 ∧
      (∀ i, i < 4 → S2.mem.readLE (A' + 8 * i) 8 = s.mem.readLE (z.toNat + 8 * i) 8) ∧
      (len = 0 ∨ s.mem.readLE (z.toNat + 8 * (len - 1)) 8 ≠ 0) ∧
      (∀ i, len ≤ i → i < 4 → s.mem.readLE (z.toNat + 8 * i) 8 = 0)) := ⟨hbP, hword, hnorm, hzero⟩
  clear hbP hword hnorm hzero
  janus_data hd [hw, hbpa, hPa]
  janus_eval_nat h_f : flagAddr
  rw [h_f] at hflag
  rcases hPrt with ⟨hL, hPo⟩ | ⟨hL, hPi⟩
  · subst hL
    have hPo16 : Outside (P + 16) 8 R.rt := Outside.of_sub hPo (by omega) (by omega)
    have hPo24 : Outside (P + 24) 8 R.rt := Outside.of_sub hPo (by omega) (by omega)
    janus_run calls [hwb2]
    all_goals (rw [← Spec.val256_limbs s.mem z.toNat])
    all_goals (unfold Hidden at hfacts)
    all_goals (obtain ⟨hbP, hword, hnorm, hzero⟩ := hfacts)
    all_goals first
      | (set_option maxHeartbeats 300000 in exact ⟨tail0_bigout (sp := s.sp.toNat) hfr2 h_rdP hPa hP48 hAacc hA48 hbP hAP hlen hword hnorm hzero,
          tail0_frame hfr2⟩)
      | (set_option maxHeartbeats 600000 in exact ⟨tail1_bigout (sp := s.sp.toNat) hfr2 h_rdP hPa hP48 hAacc hA48 hbP hAP hlen hword hnorm hzero hbpo hbpd hb'
            ‹MemFrame _ _ _› ‹LiveFrame _ _ _ _› ⟨(A', A' + 32), by simp, Nat.le_refl _, Nat.le_refl _⟩ ‹InRanges (BitVec.toNat _) 16 R.rt›
            (read_wb' ‹MemFrame _ _ _› hPo16 (by omega)) (read_wb' ‹MemFrame _ _ _› hPo24 (by omega)) (Or.symm ‹Apart (BitVec.toNat _) 16 A' 32›) ‹Apart P 32 (BitVec.toNat _) 16›,
          tail1_frame hfr2 hb' ‹MemFrame _ _ _› ‹InRanges (BitVec.toNat _) 16 R.rt›⟩)
  · subst hL
    have hPi16 : InRanges (P + 16) 8 ([(P, P + 32)] ++ [(A', A' + 32)]) :=
      ⟨(P, P + 32), by simp, by omega, by omega⟩
    have hPi24 : InRanges (P + 24) 8 ([(P, P + 32)] ++ [(A', A' + 32)]) :=
      ⟨(P, P + 32), by simp, by omega, by omega⟩
    janus_run calls [hwb2]
    all_goals (rw [← Spec.val256_limbs s.mem z.toNat])
    all_goals (unfold Hidden at hfacts)
    all_goals (obtain ⟨hbP, hword, hnorm, hzero⟩ := hfacts)
    all_goals first
      | (set_option maxHeartbeats 300000 in exact ⟨tail0_bigout (sp := s.sp.toNat) hfr2 h_rdP hPa hP48 hAacc hA48 hbP hAP hlen hword hnorm hzero,
          tail0_frame hfr2⟩)
      | (obtain ⟨hAw, hPw⟩ : Apart (BitVec.toNat _) 16 A' 32 ∧ Apart P 32 (BitVec.toNat _) 16 :=
           ⟨(‹Apart (BitVec.toNat _) 16 P 32 ∧ Apart (BitVec.toNat _) 16 A' 32›).2,
            Or.symm (‹Apart (BitVec.toNat _) 16 P 32 ∧ Apart (BitVec.toNat _) 16 A' 32›).1⟩
         have hLv : LiveFrame (M1 S2.mem P len) _ [(P, P + 32), (A', A' + 32)] [] := ‹LiveFrame _ _ _ _›
         set_option maxHeartbeats 600000 in
         exact ⟨tail1_bigout (s := s.mem) (W := S2.mem) (sp := s.sp.toNat) (bp := bp.toNat) (z := z.toNat) (P := P) (A' := A') (len := len) (rt := R.rt)
              (L1 := [(P, P + 32), (A', A' + 32)]) hfr2 h_rdP hPa hP48 hAacc hA48 hbP hAP hlen hword hnorm hzero hbpo hbpd hb'
              ‹MemFrame _ _ _› hLv ⟨(A', A' + 32), by simp, Nat.le_refl _, Nat.le_refl _⟩ ‹InRanges (BitVec.toNat _) 16 R.rt›
              (hLv.readLE (P + 16) 8 ⟨(P, P + 32), by simp, by omega, by omega⟩ trivial)
              (hLv.readLE (P + 24) 8 ⟨(P, P + 32), by simp, by omega, by omega⟩ trivial) (Or.symm hAw) hPw,
            tail1_frame (s := s.mem) (W := S2.mem) (sp := s.sp.toNat) (bp := bp.toNat) (P := P) (A' := A') (len := len) (rt := R.rt)
              hfr2 hb' ‹MemFrame _ _ _› ‹InRanges (BitVec.toNat _) 16 R.rt›⟩)

end Fv256.Arm64.IntoBig
