import Fv256.Arm64.IntoBigMid

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.IntoBig

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem correctness (impl : List Segment) (R : RtInv) (b : Nat) (z bp : BitVec 64)
    (hnew : NewobjectLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb1 : WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, bp]
      (fun s => Pre R b z bp s ∧ PreX z bp s) (fun s s' => Post R z bp s s') := by
  intro ret hret s hs hpre'
  obtain ⟨hpre, hpx⟩ := hpre'
  have hpre0 := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hflag, hty1, hty2, hok1, hok2, hok3, hok4,
    hinv, hbud, hbp, hbpo, hbpd, hz⟩ := hpre
  obtain ⟨hbpa, hbpb⟩ := hbp
  simp only [Disjoint] at hbpd
  have hblk := Janus.Contracts.AllocSat.le_blockSize 32 false
  have hblk2 := Janus.Contracts.AllocSat.le_blockSize 32 true
  janus_intro hs
  janus_data hd [hw]
  janus_eval_nat h_b : bigType
  janus_eval_nat h_a : arrType
  janus_eval_nat h_f : flagAddr
  rw [h_b] at hty1 hok1
  rw [h_a] at hty2 hok2
  rw [h_f] at hflag
  janus_run until [Extracted.entry + 0x64] calls [hnew.pos, hwb1, hwb2]
  rotate_left 2
  · refine mid impl R b z bp ret hret s hnew hwb2 hpre0 hpx ‹_› _ ?_ ?_ ?_ ?_ _ rfl (Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals (try unfold Rel)
    all_goals (try (first | exact rfl | (janus_simp; exact rfl)))
    all_goals (repeat' refine And.intro ?_ ?_)
    all_goals (try janus_simp)
    all_goals first
      | (with_reducible assumption)
      | janus_live
      | janus_frame
      | (exact ZeroBytes.writeLE_apart ‹_› (by unfold Apart at *; omega))
      | (unfold Apart at *; janus_clear_irrel2; omega)
      | (trace_state; fail "x1")
  · refine mid impl R b z bp ret hret s hnew hwb2 hpre0 hpx ‹_› _ ?_ ?_ ?_ ?_ _ rfl (Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals (try unfold Rel)
    all_goals (try (first | exact rfl | (janus_simp; exact rfl)))
    all_goals (repeat' refine And.intro ?_ ?_)
    all_goals (try janus_simp)
    all_goals first
      | (with_reducible assumption)
      | janus_live
      | janus_frame
      | (exact ZeroBytes.writeLE_apart ‹_› (by unfold Apart at *; omega))
      | (unfold Apart at *; janus_clear_irrel2; omega)
      | (refine ZeroBytes.writeLE_apart (ZeroBytes.writeLE_apart (ZeroBytes.writeLE_apart (ZeroBytes.of_liveFrame ‹LiveFrame _ _ _ []› ‹ZeroBytes _ _ _› ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _⟩) ?_) ?_) ?_ <;> (unfold Apart at *; omega))
      | (trace_state; fail "x2")
  · refine mid impl R b z bp ret hret s hnew hwb2 hpre0 hpx ‹_› _ ?_ ?_ ?_ ?_ _ rfl (Or.inl ⟨?_, ?_, ?_⟩)
    all_goals (try unfold Rel)
    all_goals (try (first | exact rfl | (janus_simp; exact rfl)))
    all_goals (repeat' refine And.intro ?_ ?_)
    all_goals (try janus_simp)
    all_goals first
      | (with_reducible assumption)
      | janus_live
      | janus_frame
      | (exact ZeroBytes.writeLE_apart ‹_› (by unfold Apart at *; omega))
      | (unfold Apart at *; janus_clear_irrel2; omega)
      | (trace_state; fail "x3")
  · refine ⟨fun _ => ?_, fun h => absurd ‹z.toNat = 0› h, ?_⟩
    all_goals (try janus_simp)
    all_goals first
      | (with_reducible assumption)
      | janus_live
      | janus_frame
      | (trace_state; fail "x4")
  · refine ⟨fun _ => ?_, fun h => absurd ‹z.toNat = 0› h, ?_⟩
    all_goals (try janus_simp)
    all_goals first
      | (with_reducible assumption)
      | janus_live
      | janus_frame
      | (trace_state; fail "x5")
end Fv256.Arm64.IntoBig
