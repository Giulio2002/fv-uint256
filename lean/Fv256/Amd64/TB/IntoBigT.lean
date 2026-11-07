import Fv256.Amd64.TB.IntoBigMid

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Amd64.IntoBig

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem correctness (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (z bp : BitVec 64)
    (hnew : NewobjectLiveContract64 ((Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).IntoBig"]).link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb1 : WbLiveContract64 ((Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).IntoBig"]).link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 ((Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).IntoBig"]).link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    Ensures ((Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).IntoBig"]).link impl) (Extracted.entry + 0x60) [z, bp]
      (fun s => Pre R b z bp s ∧ PreX z bp s) (fun s s' => Post R z bp s s') := by
  intro ret hret s hs hpre'
  obtain ⟨hpre, hpx⟩ := hpre'
  have hpre0 := hpre
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hflag, hty1, hty2, hok1, hok2, hok3, hok4,
    hinv, hbud, hbp, hbpo, hbpd, hz⟩ := hpre
  obtain ⟨hbpa, hbpb⟩ := hbp
  simp only [Janus.Spec.Disjoint] at hbpd
  janus64_intro hs
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset, Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr ⊢
  have hblk := Janus.Contracts.AllocSat.le_blockSize 32 false
  have hblk2 := Janus.Contracts.AllocSat.le_blockSize 32 true
  janus64_data hd [hw]
  janus_eval_nat h_b : bigType
  janus_eval_nat h_a : arrType
  janus_eval_nat h_f : flagAddr
  rw [h_b] at hty1 hok1
  rw [h_a] at hty2 hok2
  rw [h_f] at hflag
  janus64_run until [(Extracted.entry + 0x60) + 0x68] calls [hnew.pos, hwb1, hwb2]
  rotate_left 2
  · refine mid impl R b z bp ret hret s hnew hwb2 hpre0 hpx (show _ by janus_assumption) _ ?_ ?_ ?_ ?_ ?_ ?_ _ rfl (Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals (try unfold Rel)
    all_goals (try (first | exact rfl | (janus64_simp; exact rfl)))
    all_goals (repeat' refine And.intro ?_ ?_)
    all_goals (try janus64_simp)
    all_goals first
      | (with_reducible assumption)
      | janus_live
      | janus_frame
      | (exact ZeroBytes.writeLE_apart (show _ by janus_assumption) (by unfold Apart at *; omega))
      | (unfold Apart at *; janus_clear_irrel2; omega)
      | (trace_state; fail "x1")
  · refine mid impl R b z bp ret hret s hnew hwb2 hpre0 hpx (show _ by janus_assumption) _ ?_ ?_ ?_ ?_ ?_ ?_ _ rfl (Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals (try unfold Rel)
    all_goals (try (first | exact rfl | (janus64_simp; exact rfl)))
    all_goals (repeat' refine And.intro ?_ ?_)
    all_goals (try janus64_simp)
    all_goals first
      | (with_reducible assumption)
      | janus_live
      | janus_frame
      | (exact ZeroBytes.writeLE_apart (show _ by janus_assumption) (by unfold Apart at *; omega))
      | (unfold Apart at *; janus_clear_irrel2; omega)
      | (refine ZeroBytes.writeLE_apart (ZeroBytes.writeLE_apart (ZeroBytes.writeLE_apart (ZeroBytes.of_liveFrame (show LiveFrame _ _ _ [] by janus_assumption) (ZeroBytes.writeLE_apart (show ZeroBytes _ _ _ by janus_assumption) ?_) ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _⟩) ?_) ?_) ?_ <;> (unfold Apart at *; omega))
      | (trace_state; fail "x2")
  · refine mid impl R b z bp ret hret s hnew hwb2 hpre0 hpx (show _ by janus_assumption) _ ?_ ?_ ?_ ?_ ?_ ?_ _ rfl (Or.inl ⟨?_, ?_, ?_⟩)
    all_goals (try unfold Rel)
    all_goals (try (first | exact rfl | (janus64_simp; exact rfl)))
    all_goals (repeat' refine And.intro ?_ ?_)
    all_goals (try janus64_simp)
    all_goals first
      | (with_reducible assumption)
      | janus_live
      | janus_frame
      | (exact ZeroBytes.writeLE_apart (show _ by janus_assumption) (by unfold Apart at *; omega))
      | (unfold Apart at *; janus_clear_irrel2; omega)
      | (trace_state; fail "x3")
  · refine ⟨fun _ => ?_, fun h => absurd (show z.toNat = 0 by janus_assumption) h, ?_, fun _ => ?_⟩
    all_goals (try janus64_simp)
    all_goals first
      | (with_reducible assumption)
      | janus_live
      | janus_frame
      | (trace_state; fail "x4")
  · refine ⟨fun _ => ?_, fun h => absurd (show z.toNat = 0 by janus_assumption) h, ?_, fun _ => ?_⟩
    all_goals (try janus64_simp)
    all_goals first
      | (with_reducible assumption)
      | janus_live
      | janus_frame
      | (trace_state; fail "x5")




end Fv256.Amd64.IntoBig
