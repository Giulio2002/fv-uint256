import Fv256.Amd64.IntoBigMid
import Fv256.Amd64.CallSites.Live

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Amd64.IntoBig

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem correctness (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (z bp : BitVec 64)
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
  janus64_run until [Extracted.entry + 0x68] calls [hnew.pos, hwb1, hwb2]
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

namespace Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64

def newA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def w1A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier1")
def w2A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier2")

/-- The stub runtime: generic code placed at `Extracted.program`'s own contract addresses. -/
def implAt : List Amd64.Segment := [newobjectSeg newA, wbSeg w1A, wbSeg w2A]

/-- The requests the witness runtime serves: `IntoBig`'s. -/
def ok : Nat → List Nat → Prop := fun a args =>
  (a = newA ∧ (args = [bigType] ∨ args = [arrType])) ∨ (a = w1A ∧ args = [1]) ∨ (a = w2A ∧ args = [2])

def R : RtInv := toyR [] ok

def linked : Amd64.Program := Extracted.program.link implAt

theorem addr_new : Extracted.program.contractAddr "runtime.newobject" = newA := by decide
theorem addr_w1 : Extracted.program.contractAddr "runtime.gcWriteBarrier1" = w1A := by decide
theorem addr_w2 : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = w2A := by decide

theorem model_new : NewobjectLiveContract64 linked newA 4096 R := by janus64_live_newobject
theorem model_wb1 : WbLiveContract64 linked w1A 4096 R 1 := by janus64_live_wb 1
theorem model_wb2 : WbLiveContract64 linked w2A 4096 R 2 := by janus64_live_wb 2

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
/-- the `uint256.Int` argument (32 readable bytes) and the slot `*b` (8 writable bytes, holds nil). -/
def zA : Nat := 0x300000
def bpA : Nat := 0x300100

def dataByte (a : Nat) : Option Arm64.Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

def bytes0 (a : Nat) : Arm64.Byte :=
  match dataByte a with
  | some v => v
  | none => if a = BUMP + 3 then 0x10 else if a = sp0 + 1 then 0x10 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4128, 4152, true⟩, ⟨g0, 0x100, false⟩, ⟨flagAddr, 8, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩, ⟨zA, 32, false⟩, ⟨bpA, 8, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def zV : BitVec 64 := BitVec.ofNat 64 zA
def bpV : BitVec 64 := BitVec.ofNat 64 bpA

/-- `IntoBig(z, &b)` with `b == nil`. -/
def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then zV else if i = 3 then bpV else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [zV, bpV] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; match i, h with | 0, _ => rfl | 1, _ => rfl, rfl⟩

theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
  decide

theorem dataByte_none (a : Nat) (ha : 0x500000 ≤ a) : dataByte a = none := by
  unfold dataByte
  have : Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) = none := by
    rw [List.find?_eq_none]
    intro d hd
    have h2 : d.base + d.bytes.length < 0x500000 := by
      have : ∀ d' ∈ Extracted.data, d'.base + d'.bytes.length < 0x500000 := by decide
      exact this d hd
    simp only [Bool.not_eq_true, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right; omega
  rw [this]

theorem bytes0_bump : mem0.readLE BUMP 8 = HEAP := by decide

theorem inv0 : R.inv 0x400 [] (s0.regs 14).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init (m := mem0) (g := (s0.regs 14).toNat) (by decide) bytes0_bump (fun i hi hi' => ?_) (by decide) (by decide) (by decide)
  show bytes0 i = 0
  simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [sp0, HEAP] at *; omega)]

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

theorem bp_nil : s0.mem.readLE bpA 8 = 0 := by decide

theorem pre : Pre R 0x400 zV bpV s0 := by
  have hz : zV.toNat ≠ 0 := by decide
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, dataLoaded, ?_, ?_, ?_,
    by decide, ?_, ?_, ?_, ?_, ?_, ?_, inv0, by decide, ⟨by decide, by decide⟩, ?_, ?_, fun _ => ?_⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [Apart]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [addr_new]; exact Or.inl ⟨rfl, Or.inl rfl⟩
  · rw [addr_new]; exact Or.inl ⟨rfl, Or.inr rfl⟩
  · rw [addr_w1]; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rw [addr_w2]; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · unfold Janus.Spec.Disjoint; decide
  · refine ⟨⟨by decide, by decide⟩, ?_, ?_, ?_, fun h => absurd bp_nil h⟩
    · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
    · unfold Janus.Spec.Disjoint; decide
    · unfold Janus.Spec.Disjoint; decide

theorem preX : PreX zV bpV s0 :=
  ⟨by simp only [Apart]; decide, fun _ h => absurd bp_nil h⟩

open Fv256.CallSites

/-- The call states of the runtime stubs (U-WITNESS-CALLSITE): `s0`'s memory at the stub's entry, `RSP` at the call frame
(`s0`'s `RSP` less 32); `RAX` is the type descriptor for `runtime.newobject`. -/
def csNew : Amd64.State :=
  { s0 with rip := BitVec.ofNat 64 newA, regs := fun i => if i = 0 then BitVec.ofNat 64 bigType else if i = 4 then s0.regs 4 - 32#64 else s0.regs i }
def csW1 : Amd64.State :=
  { s0 with rip := BitVec.ofNat 64 w1A, regs := fun i => if i = 4 then s0.regs 4 - 32#64 else s0.regs i }
def csW2 : Amd64.State :=
  { s0 with rip := BitVec.ofNat 64 w2A, regs := fun i => if i = 4 then s0.regs 4 - 32#64 else s0.regs i }

theorem csNew_rip : csNew.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") := by rw [addr_new]; rfl
theorem csW1_rip : csW1.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") := by rw [addr_w1]; rfl
theorem csW2_rip : csW2.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") := by rw [addr_w2]; rfl

set_option maxRecDepth 100000 in
theorem csNew_pre : NewobjectPre64 4096 csNew ∧ StackRoom64 csNew 4096 1 ∧
    LiveAt R (Extracted.program.contractAddr "runtime.newobject") [(csNew.regs 0).toNat] [] 0x400 (newobjectRound64 csNew)
      (csNew.regs 14).toNat csNew.mem (liveWin64 csNew 4096 1) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, ?_⟩, ?_, inv0, by decide, liveSep_nil _, ?_⟩
  · simp only [calleeStack64, outside_cons, outside_nil]; rw [rt_eq]; decide
  · rw [addr_new]; exact Or.inl ⟨rfl, Or.inl rfl⟩
  · simp only [liveWin64, calleeStack64]; apply liveSep_two <;> (rw [rt_eq]; simp only [outside_cons, outside_nil]; decide)

set_option maxRecDepth 100000 in
theorem csW1_pre : CallOK64 csW1 4096 0 ∧ R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
    R.inv 0x400 [] (csW1.regs 14).toNat (view R.rt [] csW1.mem) ∧ LiveSep [] [((csW1.regs 4).toNat - 4096, (csW1.regs 4).toNat + 8)] ∧
    LiveSep [((csW1.regs 4).toNat - 4096, (csW1.regs 4).toNat + 8)] R.rt :=
  ⟨by decide, by rw [addr_w1]; exact Or.inr (Or.inl ⟨rfl, rfl⟩), inv0, liveSep_nil _,
    liveSep_one (by rw [rt_eq]; simp only [outside_cons, outside_nil]; decide)⟩

set_option maxRecDepth 100000 in
theorem csW2_pre : CallOK64 csW2 4096 0 ∧ R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
    R.inv 0x400 [] (csW2.regs 14).toNat (view R.rt [] csW2.mem) ∧ LiveSep [] [((csW2.regs 4).toNat - 4096, (csW2.regs 4).toNat + 8)] ∧
    LiveSep [((csW2.regs 4).toNat - 4096, (csW2.regs 4).toNat + 8)] R.rt :=
  ⟨by decide, by rw [addr_w2]; exact Or.inr (Or.inr ⟨rfl, rfl⟩), inv0, liveSep_nil _,
    liveSep_one (by rw [rt_eq]; simp only [outside_cons, outside_nil]; decide)⟩

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `R`), a budget and a call of
`IntoBig(z, &b)` with `b == nil` satisfying the precondition. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (z bp : BitVec 64) (ret : Nat) (s : State),
    NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      NewobjectPre64 4096 s_c ∧ StackRoom64 s_c 4096 1 ∧
      LiveAt R (Extracted.program.contractAddr "runtime.newobject") [(s_c.regs 0).toNat] L b (newobjectRound64 s_c)
        (s_c.regs 14).toNat s_c.mem (liveWin64 s_c 4096 1)) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧
      CallOK64 s_c 4096 0 ∧ R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
      R.inv b L (s_c.regs 14).toNat (view R.rt L s_c.mem) ∧ LiveSep L [((s_c.regs 4).toNat - 4096, (s_c.regs 4).toNat + 8)] ∧
      LiveSep [((s_c.regs 4).toNat - 4096, (s_c.regs 4).toNat + 8)] R.rt) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      CallOK64 s_c 4096 0 ∧ R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
      R.inv b L (s_c.regs 14).toNat (view R.rt L s_c.mem) ∧ LiveSep L [((s_c.regs 4).toNat - 4096, (s_c.regs 4).toNat + 8)] ∧
      LiveSep [((s_c.regs 4).toNat - 4096, (s_c.regs 4).toNat + 8)] R.rt) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, bp] s ∧
    Pre R b z bp s ∧ PreX z bp s ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R z bp s s' := by
  refine ⟨implAt, R, 0x400, zV, bpV, ret, s0, ?w0, ?w1, ?w2, ⟨[], 0x400, csNew, csNew_rip, csNew_pre⟩, ⟨[], 0x400, csW1, csW1_rip, csW1_pre⟩, ⟨[], 0x400, csW2, csW2_rip, csW2_pre⟩, hret, setup, pre, preX,
    correctness implAt R 0x400 zV bpV ?w0 ?w1 ?w2 ret hret s0 setup ⟨pre, preX⟩⟩
  case w0 => exact by rw [addr_new]; exact model_new
  case w1 => exact by rw [addr_w1]; exact model_wb1
  case w2 => exact by rw [addr_w2]; exact model_wb2

end Witness


end Fv256.Amd64.IntoBig
