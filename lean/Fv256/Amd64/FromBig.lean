import Fv256.Amd64.CallSites.Live
import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.SumC64
import Fv256.Amd64.FromBigSfb

/-!
# `uint256.FromBig(b *big.Int) (*Int, bool)` (amd64)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.FromBig

def intType : Nat := dataBase Extracted.program 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem correctness (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (x pw len : BitVec 64)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [x]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 4136 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4136) 4160 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        H [intType] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt s.mem) ∧
        (x.toNat ≠ 0 → Buffer s x 32 false ∧ s.mem.readLE x.toNat 1 < 2 ∧
          s.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (x.toNat + 16) 8 = len.toNat ∧
          Buffer s pw (8 * len.toNat) false ∧ Outside x.toNat 32 rt ∧ Outside pw.toNat (8 * len.toNat) rt ∧
          (x.toNat + 32 ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ x.toNat) ∧
          (pw.toNat + 8 * len.toNat ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ pw.toNat)))
      (fun s s' => (x.toNat = 0 → s'.regs 0 = 0 ∧ s'.regs 3 = 0) ∧
        (x.toNat ≠ 0 → ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
          s'.mem.accessible ptr 32 true = true ∧
          s'.mem.readLE ptr 32 =
            Fv256.C.fromBig (s.mem.readLE x.toNat 1 == 1)
              (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
          (s'.regs 3).toNat % 256 = (if Fv256.C.fromBigOv len.toNat then 1 else 0) ∧
          MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]))) := by
  intro ret hret s hs ⟨hg, ⟨hb, ha, hw⟩, hd, hout, hal, hH, hxx⟩
  janus64_intro hs
  janus_eval_nat h_pt : intType
  rw [h_pt] at hH
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw hout hal hxx ⊢
  janus64_data hd [hw]
  janus64_run until [Extracted.entry + 0x25] calls [hnew.pos]
  · exact fun h => h.elim
  · obtain ⟨hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9⟩ := hxx hbr
    obtain ⟨hxw, hxa⟩ := hx1
    obtain ⟨hpw, hpa⟩ := hx5
    have hdx := InRanges.disjoint ‹InRanges _ 32 rt› hx6
    have hdp := InRanges.disjoint ‹InRanges _ 32 rt› hx7
    have hds := InRanges.disjoint ‹InRanges _ 32 rt› hout
    janus64_run calls [Fv256.Amd64.FromBigSfb.sfb_summary impl _ x pw len]
    rename_i wa wb wc wd we wf wg wh hfr hin hle hacc h8 h16 hz rr a cpc csp c28 c29 c30 c18 cfs cfr cflag cval
    refine ⟨fun h => h.elim, _, rfl, hin, h16, hacc, ?_, cflag, ?_⟩
    · rw [Util.readLE_32]
      rw [Fv256.C.bigAbs_write, Fv256.C.bigAbs_write, Fv256.C.bigAbs_frame _ _ _ _ _ hfr, Fv256.C.bigAbs_write,
        Fv256.C.bigAbs_write, Fv256.C.bigAbs_write] at cval
      · exact cval
      all_goals first
        | omega
        | (simp only [outside_append, outside_cons, outside_nil, and_true]
           exact ⟨hx7, by omega, by omega⟩)
    · janus_frame

/-! ## Non-vacuity: the allocation contract and the precondition are jointly satisfiable

As Janus' `AllocSatAmd64`: `mov $0x10000, %eax; ret` placed at `runtime.newobject` returns the start of a zeroed 64 KiB heap;
`H` says the argument is a type descriptor of at most 32 KiB inside `rt` and the heap is writable and zero; `hnew` is proved by
running that code; `s0` is a concrete call of `FromBig` on the big.Int `-(5 + 2^64)`; `fires` applies `correctness`. -/
namespace Witness

open Janus.Contracts.AllocSatAmd64 (ret_of)
open Janus.Contracts.AllocSat (le_blockSize)

def heap : Nat := 0x10000
def tyA : Nat := janus_eval% intType
def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def rt : List (Nat × Nat) := [(heap, heap + 0x10000), (tyA, tyA + 16)]

def impl : List Janus.Amd64.Segment :=
  [{ name := "witness.newobject", base := cA, bytes := [0xb8, 0x00, 0x00, 0x01, 0x00, 0xc3] }]

def H : RtReady := fun args _ _ v =>
  (v.accessible heap 0x10000 true = true ∧ ZeroBytes v heap 0x10000) ∧
    ∃ typ, args = [typ] ∧ InRanges typ 16 rt ∧ typSize v typ ≤ 32768

def linked : Janus.Amd64.Program := Extracted.program.link impl

theorem addr : Extracted.program.contractAddr "runtime.newobject" = cA := by decide

theorem hnew : NewobjectContract64 (Extracted.program.link impl)
    (Extracted.program.contractAddr "runtime.newobject") rt 4096 H := by
  rw [addr]
  intro s hpc ⟨⟨⟨hra, hal, _, _, _⟩, _, _⟩, hr, typ, hargs, hin, hsz⟩
  simp only [List.cons.injEq, and_true] at hargs
  subst hargs
  change ReachesRet linked _ s _
  janus64_run
  refine ⟨BitVec.ofNat 64 heap, _, _, _, _, _, _, _, ret_of s _ [BitVec.ofNat 64 heap]
    (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF, heap]) (by simp) (by simp) rfl rfl rfl rfl rfl,
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
  unfold typSize at hsz
  rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
  change typSize s.mem (s.regs 0).toNat ≤ 32768 at hsz
  have hb := blockSize_le_maxSmallSize (typSize s.mem (s.regs 0).toNat)
    (typNoscan s.mem (s.regs 0).toNat) hsz
  simp only [maxSmallSize] at hb
  have hle := le_blockSize (typSize s.mem (s.regs 0).toNat) (typNoscan s.mem (s.regs 0).toNat)
  have hheap : (BitVec.ofNat 64 heap).toNat = heap := by decide
  rw [hheap]
  obtain ⟨hacc, hz⟩ := hr
  rw [rtView_accessible] at hacc
  have hz' := ZeroBytes.of_rtView hz ⟨(heap, heap + 0x10000), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨⟨(heap, heap + 0x10000), by simp [rt], Nat.le_refl _, by simp only [heap]; omega⟩,
    by simp only [heap]; omega, Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    fun _ => by decide, fun _ _ => by decide, fun _ => fun i hi => hz' i (by omega), hle⟩

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def dsegs : List DataSegment := Extracted.data

def bytes (a : Nat) : Byte :=
  if a = sp0 + 2 then 0x20 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => BitVec.ofNat 8 ((Fv256.C.bigEntries.lookup a).getD 0)

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def xp : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigBase
def pw : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigWords

def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 0 then xp else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 4136, 4136 + 24, true⟩, ⟨g0, 0x100, false⟩, ⟨heap, 0x10000, true⟩, ⟨0x30800, 0x100, false⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [xp] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Janus.Amd64.Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH : H [intType] (s0.regs 14).toNat ((s0.regs 4).toNat - 40) (rtView rt s0.mem) := by
  have hpt : intType = tyA := by unfold tyA; decide
  rw [hpt]
  have hbase : ∀ d ∈ dsegs, 0x20000 ≤ d.base := by simp only [dsegs]; decide
  refine ⟨⟨by rw [rtView_accessible]; decide, fun i hi => ?_⟩, tyA, rfl,
    ⟨(tyA, tyA + 16), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩, by decide⟩
  show (if _ then bytes (heap + i) else 0) = 0
  split
  · have h1 : dsegs.find? (fun d => decide (d.base ≤ heap + i ∧ heap + i < d.base + d.bytes.length)) = none := by
      rw [List.find?_eq_none]
      intro d hd
      have := hbase d hd
      have hh : heap + i < 0x20000 := by simp only [heap]; omega
      simp only [decide_eq_true_eq]
      omega
    have h3 : heap + i ≠ sp0 + 2 := by simp only [heap, sp0]; omega
    simp only [bytes, if_neg h3, h1]
    have h2 : Fv256.C.bigEntries.lookup (heap + i) = none := Fv256.C.bigEntries_none _ (by simp only [heap]; omega)
    rw [h2]; rfl
  · rfl

set_option maxRecDepth 100000 in
theorem pre : StackGuardOK s0 0 ∧ StackWritable s0 4136 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 4).toNat - 4136) 4160 rt ∧ (s0.regs 4).toNat % 8 = 0 ∧
    H [intType] (s0.regs 14).toNat ((s0.regs 4).toNat - 40) (rtView rt s0.mem) ∧
    (xp.toNat ≠ 0 → Buffer s0 xp 32 false ∧ s0.mem.readLE xp.toNat 1 < 2 ∧
      s0.mem.readLE (xp.toNat + 8) 8 = pw.toNat ∧ s0.mem.readLE (xp.toNat + 16) 8 = (2 : BitVec 64).toNat ∧
      Buffer s0 pw (8 * (2 : BitVec 64).toNat) false ∧ Outside xp.toNat 32 rt ∧ Outside pw.toNat (8 * (2 : BitVec 64).toNat) rt ∧
      (xp.toNat + 32 ≤ (s0.regs 4).toNat - 4136 ∨ (s0.regs 4).toNat + 24 ≤ xp.toNat) ∧
      (pw.toNat + 8 * (2 : BitVec 64).toNat ≤ (s0.regs 4).toNat - 4136 ∨ (s0.regs 4).toNat + 24 ≤ pw.toNat)) := by
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, outside_cons, outside_nil]; decide, by decide, hH, fun _ => ?_⟩
  refine ⟨⟨by decide, by decide⟩, by decide, by decide, by decide, ⟨by decide, by decide⟩, ?_, ?_, by decide, by decide⟩
  · simp only [rt, outside_cons, outside_nil]; decide
  · simp only [rt, outside_cons, outside_nil]; decide

/-- pins the type of an existential variable of `nonvacuous` -/
def pinBitVec64 (_k : BitVec 64) : Prop := True

/-- The call state of `runtime.newobject` (U-WITNESS-CALLSITE): `s0`'s memory, at the allocator's entry, `RSP` at the call
frame (`s0`'s `RSP` less 40), `RAX` the type descriptor. -/
def csNew : Janus.Amd64.State :=
  { s0 with rip := BitVec.ofNat 64 cA, regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else if i = 4 then s0.regs 4 - 40#64 else s0.regs i }

theorem csNew_rip : csNew.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") := by rw [addr]; rfl

set_option maxRecDepth 100000 in
theorem csNew_pre : NewobjectPre64 4096 csNew ∧ Ready64 H rt [(csNew.regs 0).toNat] csNew := by
  have ht : (csNew.regs 0).toNat = intType := by
    have : intType = tyA := by unfold tyA; decide
    rw [this]; decide
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  show H [(csNew.regs 0).toNat] _ _ (rtView rt s0.mem)
  rw [ht]; exact hH

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `rt`, `H`), the contract hypotheses, an admissible
return address, a call state and the precondition. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (x : BitVec 64) (pw : BitVec 64) (len : BitVec 64) (ret : Nat) (s : State),
    NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    (∃ s_c : Janus.Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      (NewobjectPre64 4096 s_c ∧ Ready64 H rt [(s_c.regs 0).toNat] s_c)) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [x] s ∧
    (pinBitVec64 pw ∧
    pinBitVec64 len ∧
    StackGuardOK s 0 ∧ StackWritable s 4136 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4136) 4160 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        H [intType] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt s.mem) ∧
        (x.toNat ≠ 0 → Buffer s x 32 false ∧ s.mem.readLE x.toNat 1 < 2 ∧
          s.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (x.toNat + 16) 8 = len.toNat ∧
          Buffer s pw (8 * len.toNat) false ∧ Outside x.toNat 32 rt ∧ Outside pw.toNat (8 * len.toNat) rt ∧
          (x.toNat + 32 ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ x.toNat) ∧
          (pw.toNat + 8 * len.toNat ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ pw.toNat))) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ (x.toNat = 0 → s'.regs 0 = 0 ∧ s'.regs 3 = 0) ∧
        (x.toNat ≠ 0 → ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
          s'.mem.accessible ptr 32 true = true ∧
          s'.mem.readLE ptr 32 =
            Fv256.C.fromBig (s.mem.readLE x.toNat 1 == 1)
              (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
          (s'.regs 3).toNat % 256 = (if Fv256.C.fromBigOv len.toNat then 1 else 0) ∧
          MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)])) := by
  refine ⟨impl, rt, H, xp, pw, 2, ret, s0, hnew, ⟨csNew, csNew_rip, csNew_pre⟩, hret, setup, ?w3,
    correctness impl rt H xp pw 2 hnew ret hret s0 setup ?w3⟩
  case w3 => exact ⟨trivial, trivial, pre⟩

end Witness

end Fv256.Amd64.FromBig
