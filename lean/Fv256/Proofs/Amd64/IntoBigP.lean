import Fv256.Proofs.Amd64.IntoBigDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Amd64.IntoBig

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem probe (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (z bp : BitVec 64)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb1 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, bp]
      (fun s => Pre R b z bp s ∧ PreX z bp s) (fun s s' => Post R z bp s s') := by
  intro ret hret s hs hpre'
  obtain ⟨hpre, hpx⟩ := hpre'
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
  janus64_run until [Extracted.entry + 0x68] calls [hnew.pos, hwb1, hwb2]
  rotate_left 2
  · trace_state; fail "mid1"
  · trace_state; fail "mid2"
  · trace_state; fail "mid3"
  all_goals (refine ⟨fun _ => ?_, fun h => absurd ‹z.toNat = 0› h, ?_, fun _ => ?_⟩)
  all_goals (try janus64_simp)
  all_goals first
    | (with_reducible assumption)
    | janus_live
    | janus_frame
    | (trace_state; fail "post")

end Fv256.Amd64.IntoBig
