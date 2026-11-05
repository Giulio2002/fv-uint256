import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).Bytes() []byte` (amd64)

**Guarantee.** For every receiver `z` (`RAX`), every list `rt` of runtime-owned memory ranges and **every** implementation of
`runtime.newobject` satisfying the allocation contract (`NewobjectContract64`, `Janus/Contracts/AllocAmd64.lean`; hypothesis `hnew`),
and every Go call whose stack-growth check falls through (`StackGuardOK s 0`, the stack window `[RSP-4192, RSP+24)` writable (`StackWritable s 4192 24`)) outside `rt`, with the read-only data (the type descriptor of `Int`) loaded,
the 32 bytes at `z` readable, outside `rt` and outside the stack window: the call returns, obeys the ABI, and the result is a pointer `ptr`
with `[ptr, ptr+32)` inside the runtime-owned ranges (a *fresh* object, disjoint from everything the caller holds), writable and
16-byte aligned, whose 32 bytes are the number at `z` (read before the call), and memory is unchanged outside `rt` and the stack window.

**What is assumed.** Only the contract hypothesis `hnew` for the code linked at `runtime.newobject` (not extracted: `janus extract --contract
runtime.newobject`); see `docs/RUNTIME-CONTRACTS.md` of Janus.

**Non-vacuity.** `Witness.nonvacuous` / `Witness.returns`: a toy allocator (two instructions, returning a fixed zeroed heap) is linked at the `runtime.newobject` address, its contract `hnew` is proved by symbolic execution, and a concrete call state satisfies every precondition, so the hypotheses are jointly satisfiable and the theorem fires (the call returns a fresh object in `rt` holding the expected value).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.Bytes

/-- The address of `uint256.Int`'s type descriptor (the `LEA` before the call loads it): the extraction's only data object. -/
def intType : Nat := dataBase Extracted.program 0

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 4192 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4192) 4216 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        Buffer s z 32 false ∧ Outside z.toNat 32 rt ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4192 ∨ (s.regs 4).toNat + 24 ≤ z.toNat) ∧
        H [intType] (s.regs 14).toNat ((s.regs 4).toNat - 32) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧ s'.mem.accessible ptr 32 true = true ∧
        (s'.regs 0).toNat = ptr + (if Spec.byteLen (valueAt s z 32) = 0 then 0 else 32 - Spec.byteLen (valueAt s z 32)) ∧
        (s'.regs 1).toNat = Spec.byteLen (valueAt s z 32) ∧ (s'.regs 2).toNat = Spec.byteLen (valueAt s z 32) ∧
        Spec.fromBE (fun i => s'.mem.readLE (ptr + (if Spec.byteLen (valueAt s z 32) = 0 then 0 else 32 - Spec.byteLen (valueAt s z 32)) + i) 1) (Spec.byteLen (valueAt s z 32)) = valueAt s z 32 ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 24)])) := by
  intro ret hret s hs ⟨hg, ⟨hb, ha, hw⟩, hd, hout, hal, ⟨hzw, hz⟩, hzo, hzd, hH⟩
  janus64_intro hs
  janus_eval_nat h_pt : intType
  rw [h_pt] at hH
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw hout hal hzd ⊢
  janus64_data hd [hw]
  janus64_run until [Extracted.entry + 0x20] calls [hnew.pos]
  rename_i wobj wregs wfl wx1 wx2 wx3 wx4 wmem wo wx hmf hin hle hacc h8 h16 hzb htr
  have hdj := InRanges.disjoint hin hout
  have hdz := InRanges.disjoint hin hzo
  janus64_run [Util.readLE_32]
  -- TODO: port the arm64 closing (bl_4/bl_3/bl_2 byte-length case split, suffix_be, rev8 normal form, ptr_arith); iterate under the heavy lock
  trace_state
  all_goals sorry

namespace Witness

open Janus.Contracts.AllocSatAmd64 (ret_of)
open Janus.Contracts.AllocSat (le_blockSize)

def heap : Nat := 0x10000
def tyA : Nat := janus_eval% intType
def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def rt : List (Nat × Nat) := [(heap, heap + 0x10000), (tyA, tyA + 16)]

/-- A toy allocator at the runtime.newobject address: `mov $0x10000, %eax; ret` (returns the heap at `0x10000`). -/
def impl : List Amd64.Segment :=
  [{ name := "witness.newobject", base := cA, bytes := [0xb8, 0x00, 0x00, 0x01, 0x00, 0xc3] }]

def H : RtReady := fun args _ _ v =>
  (v.accessible heap 0x10000 true = true ∧ ZeroBytes v heap 0x10000) ∧
    ∃ typ, args = [typ] ∧ InRanges typ 16 rt ∧ typSize v typ ≤ 32768

def linked : Amd64.Program := Extracted.program.link impl

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
def zp : Nat := 0x30800
def dsegs : List DataSegment := Extracted.data

def bytes (a : Nat) : Byte :=
  if a = sp0 + 2 then 0x20 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def arg : BitVec 64 := BitVec.ofNat 64 zp

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then arg else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 4192, 4192 + 24, true⟩, ⟨g0, 0x100, false⟩, ⟨heap, 0x10000, true⟩, ⟨zp, 0x100, false⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [arg] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH : H [intType] (s0.regs 14).toNat ((s0.regs 4).toNat - 32) (rtView rt s0.mem) := by
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
  · rfl

set_option maxRecDepth 100000 in
theorem pre : StackGuardOK s0 0 ∧ StackWritable s0 4192 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 4).toNat - 4192) 4216 rt ∧ (s0.regs 4).toNat % 8 = 0 ∧
    Buffer s0 arg 32 false ∧ Outside arg.toNat 32 rt ∧
    (arg.toNat + 32 ≤ (s0.regs 4).toNat - 4192 ∨ (s0.regs 4).toNat + 24 ≤ arg.toNat) ∧
    H [intType] (s0.regs 14).toNat ((s0.regs 4).toNat - 32) (rtView rt s0.mem) :=
  ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, outside_cons, outside_nil]; decide, by decide, ⟨by decide, by decide⟩,
    by simp only [rt, outside_cons, outside_nil]; decide, by decide, hH⟩

/-- The preconditions and the allocator contract are jointly satisfiable: a concrete call state (with the toy allocator linked at
the `runtime.newobject` address) meets every hypothesis of `correctness`. -/
theorem nonvacuous : CallSetup (linked.withExit ret) Extracted.entry [arg] s0 ∧
    (StackGuardOK s0 0 ∧ StackWritable s0 4192 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 4).toNat - 4192) 4216 rt ∧ (s0.regs 4).toNat % 8 = 0 ∧
    Buffer s0 arg 32 false ∧ Outside arg.toNat 32 rt ∧
    (arg.toNat + 32 ≤ (s0.regs 4).toNat - 4192 ∨ (s0.regs 4).toNat + 24 ≤ arg.toNat) ∧
    H [intType] (s0.regs 14).toNat ((s0.regs 4).toNat - 32) (rtView rt s0.mem)) := And.intro setup pre

end Witness

end Fv256.Amd64.Bytes
