import Extracted
import Fv256.Amd64.CallSites.Live
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC

/-!
# `(*uint256.Int).MarshalSSZ() ([]byte, error)` (amd64)

Same guarantee as the arm64 theorem: the slice `(ptr, 32, 32)` (`RAX`, `RBX`, `RCX`) and a nil error (`RDI`, `RSI`), with a fresh
object `[ptr, ptr+32)` inside `rt` holding the little-endian encoding of the number at `z`, under the pinned `makeslice` contract.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.MarshalSSZ

def byteType : Nat := dataBase Extracted.program 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem correctness (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hmk : MakesliceContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 4136 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4136) 4160 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        Buffer s z 32 false ∧ Outside z.toNat 32 rt ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ z.toNat) ∧
        H [byteType, 0, 32] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 3).toNat = 32 ∧ (s'.regs 1).toNat = 32 ∧
        s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧ InRanges ptr 32 rt ∧ s'.mem.accessible ptr 32 true = true ∧
        s'.mem.readLE ptr 32 = valueAt s z 32 ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)])) := by
  intro ret hret s hs ⟨hg, ⟨hb, ha, hw⟩, hd, hout, hal, ⟨hzw, hz⟩, hzo, hzd, hH⟩
  janus64_intro hs
  janus_eval_nat h_pt : byteType
  rw [h_pt] at hH
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw hout hal hzd ⊢
  janus64_data hd [hw]
  janus64_run until [Extracted.entry + 0x26] calls [hmk.pos]
  have hdj := InRanges.disjoint ‹InRanges _ 32 rt› hout
  have hdz := InRanges.disjoint ‹InRanges _ 32 rt› hzo
  janus64_run [Util.readLE_32]
  rename_i wa wb wc wd we wf wg wh hfr hin hle hacc h8 h16 hz rr
  refine ⟨_, rfl, hin, hacc, ?_, ?_⟩
  · simp only [valueAt, Util.readLE_32]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
      Util.readLE8_mod, Nat.reducePow]
  · janus_frame

/-! ## Non-vacuity: the allocation contract and the precondition are jointly satisfiable

As Janus' `AllocSatAmd64`: `mov $0x10000, %eax; ret` placed at `runtime.newobject` returns the start of a zeroed 64 KiB heap;
`H` says the argument is a type descriptor of at most 32 KiB inside `rt` and the heap is writable and zero; `hnew` is proved by
running that code; `s0` is a concrete call of `MarshalSSZ` on the big.Int `-(5 + 2^64)`; `fires` applies `correctness`. -/
namespace Witness

open Janus.Contracts.AllocSatAmd64 (ret_of)
open Janus.Contracts.AllocSat (le_blockSize)

def heap : Nat := 0x10000
def tyA : Nat := janus_eval% byteType
def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.makeslice")
def rt : List (Nat × Nat) := [(heap, heap + 0x10000), (tyA, tyA + 16)]

def impl : List Janus.Amd64.Segment :=
  [{ name := "witness.newobject", base := cA, bytes := [0xb8, 0x00, 0x00, 0x01, 0x00, 0xc3] }]

def H : RtReady := fun args _ _ v =>
  (v.accessible heap 0x10000 true = true ∧ ZeroBytes v heap 0x10000) ∧
    ∃ et l c, args = [et, l, c] ∧ InRanges et 16 rt ∧ typSize v et * c ≤ 32768

def linked : Janus.Amd64.Program := Extracted.program.link impl

theorem addr : Extracted.program.contractAddr "runtime.makeslice" = cA := by decide

theorem hmk : MakesliceContract64 (Extracted.program.link impl)
    (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H := by
  rw [addr]
  intro s hpc ⟨⟨⟨hra, hal, _, _, _⟩, _, _⟩, hr, et, l, c, hargs, hin, hsz⟩
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, -, rfl⟩ := hargs
  change ReachesRet linked _ s _
  janus64_run
  refine ⟨BitVec.ofNat 64 heap, _, _, _, _, _, _, _, ret_of s _ [BitVec.ofNat 64 heap]
    (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF, heap]) (by simp) (by simp) rfl rfl rfl rfl rfl,
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
  unfold typSize at hsz
  rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
  change typSize s.mem (s.regs 0).toNat * (s.regs 1).toNat ≤ 32768 at hsz
  have hb := blockSize_le_maxSmallSize (typSize s.mem (s.regs 0).toNat * (s.regs 1).toNat)
    (typNoscan s.mem (s.regs 0).toNat) hsz
  simp only [maxSmallSize] at hb
  have hle := le_blockSize (typSize s.mem (s.regs 0).toNat * (s.regs 1).toNat) (typNoscan s.mem (s.regs 0).toNat)
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

def zp : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigBase

def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 0 then zp else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 4136, 4136 + 24, true⟩, ⟨g0, 0x100, false⟩, ⟨heap, 0x10000, true⟩, ⟨0x30800, 0x100, false⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [zp] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Janus.Amd64.Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH : H [byteType, 0, 32] (s0.regs 14).toNat ((s0.regs 4).toNat - 40) (rtView rt s0.mem) := by
  have hpt : byteType = tyA := by unfold tyA; decide
  rw [hpt]
  have hbase : ∀ d ∈ dsegs, 0x20000 ≤ d.base := by simp only [dsegs]; decide
  refine ⟨⟨by rw [rtView_accessible]; decide, fun i hi => ?_⟩, tyA, 0, 32, rfl,
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
    Buffer s0 zp 32 false ∧ Outside zp.toNat 32 rt ∧
    (zp.toNat + 32 ≤ (s0.regs 4).toNat - 4136 ∨ (s0.regs 4).toNat + 24 ≤ zp.toNat) ∧
    H [byteType, 0, 32] (s0.regs 14).toNat ((s0.regs 4).toNat - 40) (rtView rt s0.mem) := by
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, outside_cons, outside_nil]; decide, by decide, ⟨by decide, by decide⟩,
    by simp only [rt, outside_cons, outside_nil]; decide, by decide, hH⟩

-- CALLSITE-BLOCK MarshalSSZ.mk
/-- The call state of `runtime.makeslice` (U-WITNESS-CALLSITE): `makeslice(uint8, 0, 32)` at its entry in the caller's frame (`RSP = sp0 - 40`, as in `hH`). -/
def csMk0 : Janus.Amd64.State :=
  { s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else if i = 3 then 0#64 else if i = 1 then 32#64 else if i = 4 then BitVec.ofNat 64 (sp0 - 40) else s0.regs i }
def csMk : Janus.Amd64.State := { csMk0 with rip := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") }

open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem csMk_pre : MakesliceSite H rt 4096 csMk := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide⟩, ?_⟩
  have e0 : (csMk.regs 0).toNat = byteType := by
    have hpt : byteType = tyA := by unfold tyA; decide
    rw [hpt]; decide
  have e1 : (csMk.regs 3).toNat = 0 := by decide
  have e2 : (csMk.regs 1).toNat = 32 := by decide
  have e3 : (csMk.regs 14).toNat = (s0.regs 14).toNat := by decide
  have e4 : (csMk.regs 4).toNat = (s0.regs 4).toNat - 40 := by decide
  show H [(csMk.regs 0).toNat, (csMk.regs 3).toNat, (csMk.regs 1).toNat] (csMk.regs 14).toNat (csMk.regs 4).toNat (rtView rt csMk.mem)
  rw [e0, e1, e2, e3, e4]
  exact hH

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `rt`, `H`), the contract hypotheses, an admissible
return address, a call state and the precondition. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (ret : Nat) (s : State),
    MakesliceContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 4136 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4136) 4160 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        Buffer s z 32 false ∧ Outside z.toNat 32 rt ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ z.toNat) ∧
        H [byteType, 0, 32] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt s.mem)) ∧
    (∃ s_c : Janus.Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧ Fv256.CallSites.MakesliceSite H rt 4096 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 3).toNat = 32 ∧ (s'.regs 1).toNat = 32 ∧
        s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧ InRanges ptr 32 rt ∧ s'.mem.accessible ptr 32 true = true ∧
        s'.mem.readLE ptr 32 = valueAt s z 32 ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]) :=
  ⟨impl, rt, H, zp, ret, s0, hmk, hret, setup, pre,
    ⟨csMk, rfl, csMk_pre⟩,
    correctness impl rt H zp hmk ret hret s0 setup pre⟩
end Witness

end Fv256.Amd64.MarshalSSZ
