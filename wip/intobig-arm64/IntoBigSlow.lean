import Fv256.Arm64.IntoBigFinF
import Fv256.Arm64.IntoBigClose

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.IntoBig

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- The allocating path (`cap(words) < 4`): a fresh `[4]Word`, the copy, the normalization, the stores. -/
theorem slowPath (impl : List Segment) (R : RtInv) (b : Nat) (z bp : BitVec 64) (ret : Nat)
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
    (hinv : R.inv b0 L0 (s.regs 28).toNat (view R.rt L0 S.mem)) (hb0 : 32 ≤ b0)
    (hPfr : InRanges P 32 (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24), (bp.toNat, bp.toNat + 8),
      (s.mem.readLE bp.toNat 8, s.mem.readLE bp.toNat 8 + 32),
      (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8, s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8 + 32)])) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R z bp s s') := by
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
  all_goals (subst hL)
  all_goals (try (have hPsa := hX.apart hout; unfold Apart at hPsa))
  all_goals (janus_run calls [hnew.pos, hwb2])
  all_goals (unfold Hidden at hfacts)
  all_goals (obtain ⟨hzb, hzo, hPb, hPz, hbpo', hbpd', hzd⟩ := hfacts)
  all_goals (refine ⟨fun h => absurd h hz0, fun _ => ⟨P, ?_⟩, ?_⟩)
  -- the goals come in pairs per leaf: BigOut, then MemFrame
  all_goals (first
    | (refine slow0_bigout ?hsp ?hF ?hfr ?h_rdP ?hbpo ?hbpd ?hzo ?hzd ?hzb ?hPa ?hP48 ?hAacc ?hA48 ?hbA ?hbP ?hAP ?hlen ?hv ?hnorm ?hzero ?hv0 ?hv1 ?hv2 ?hv3
       all_goals (try assumption)
       all_goals (trace_state; fail "slow0b"))
    | (refine slow0_frame ?hsp ?hF ?hfr ?hAin ?hPin
       all_goals (try assumption)
       all_goals (trace_state; fail "slow0f")))

end Fv256.Arm64.IntoBig
