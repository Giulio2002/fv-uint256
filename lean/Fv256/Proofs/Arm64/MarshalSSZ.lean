import Extracted
import Fv256.Proofs.Arm64.CallSites.Base
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.SpecC
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.UtilC
import Fv256.Spec.Arm64.MarshalSSZ

/-!
# `(*uint256.Int).MarshalSSZ() ([]byte, error)` (arm64)

**Guarantee.** For every receiver `z`, every `rt` and every implementation of `runtime.makeslice` meeting the pinned allocation
contract (`MakesliceContract`, hypothesis `hmk`), and every call whose stack check falls through, with the 32 bytes at `z`
readable and outside `rt` and the stack window: the call returns the slice `(ptr, 32, 32)` and a nil error, where `[ptr, ptr+32)` is
a fresh object inside `rt` holding the 32 bytes of the little-endian (SSZ) encoding of the number at `z`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.MarshalSSZ

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem correctness_proof (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hmk : MakesliceContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧ Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧
        Disjoint z.toNat 32 (s.sp.toNat - 4144) 4168 ∧
        H [byteType, 0, 32] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 1).toNat = 32 ∧ (s'.regs 2).toNat = 32 ∧
        s'.regs 3 = 0 ∧ s'.regs 4 = 0 ∧ InRanges ptr 32 rt ∧ s'.mem.accessible ptr 32 true = true ∧
        s'.mem.readLE ptr 32 = val256 s.mem z.toNat ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, ⟨hz, hz'⟩, hzo, hzd, hH⟩
  janus_intro hs
  janus_eval_nat h_pt : byteType
  rw [h_pt] at hH
  janus_data hd [hw]
  simp only [Disjoint] at hzd
  janus_run until [Extracted.entry + 0x30] calls [hmk.pos]
  have hdj := InRanges.disjoint ‹InRanges _ 32 rt› hout
  have hdz := InRanges.disjoint ‹InRanges _ 32 rt› hzo
  janus_run
  rename_i wa wb wc wd we wf wg hfr hin hle hacc h8 h16 hz rr
  refine ⟨_, rfl, hin, hacc, ?_, ?_⟩
  · simp only [val256, Util.readLE_32]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
      Util.readLE8_mod, Nat.reducePow]
  · janus_frame

/-! ## Non-vacuity: the allocation contract and the precondition are jointly satisfiable

Same pattern as Janus' `audit/round9/controls/NewPair_witness.lean`: a two-instruction allocator placed at
`runtime.newobject` (`MOVZ X0, #1, LSL #16; RET`) returns the start of a 64 KiB zeroed heap; `H` says the argument is a type
descriptor of at most 32 KiB inside `rt`; `hnew` is proved by running that code; `s0` is a concrete call of `MarshalSSZ`
on the big.Int `-(5 + 2^64)` satisfying the whole precondition. `fires` applies `correctness` to it. -/
namespace Wit

open Janus.Contracts.IfaceModel

def heap : Nat := 0x10000
def tyA : Nat := janus_eval% byteType
def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.makeslice")
def rt : List (Nat × Nat) := [(heap, heap + 0x10000), (tyA, tyA + 16)]

def impl : List Segment :=
  [{ name := "witness.newobject", base := cA, words := [0xd2a00020, 0xd65f03c0] }]

def H : RtReady := fun args _ _ v =>
  ∃ et l c, args = [et, l, c] ∧ InRanges et 16 rt ∧ typSize v et * c ≤ 32768 ∧
    v.accessible heap 0x10000 true = true ∧ ZeroBytes v heap 0x10000

def linked : Program := Extracted.program.link impl

theorem addr : Extracted.program.contractAddr "runtime.makeslice" = cA := by decide

theorem callRegs_eq (r : Nat → W64) :
    callRegs r r [BitVec.ofNat 64 heap] = setReg r 0 (BitVec.ofNat 64 heap) := by
  funext i
  simp only [callRegs, setReg]
  rcases i with _ | i
  · rfl
  · simp only [List.getD_cons_succ, List.getD_nil]
    split <;> rfl

theorem hmk : MakesliceContract (Extracted.program.link impl)
    (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H := by
  rw [addr]
  intro s hpc ⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩, et, l, c, hargs, hin, hsz, hacc, hz⟩
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, -, rfl⟩ := hargs
  change ReachesRet linked _ s _
  janus_run
  refine ⟨BitVec.ofNat 64 heap, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_, ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩,
    fun hpos => ?_⟩
  · simp only [retStateX]; rw [callRegs_eq]; rfl
  · unfold typSize at hsz
    rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
    change typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat ≤ 32768 at hsz
    have hb := blockSize_le_maxSmallSize (typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat)
      (typNoscan s.mem (s.regs 0).toNat) hsz
    have hle : typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat ≤
        blockSize (typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat) (typNoscan s.mem (s.regs 0).toNat) := by
      unfold blockSize; split
      · exact Nat.le_refl _
      · exact le_roundupsize _ _
    simp only [maxSmallSize] at hb
    have hheap : (BitVec.ofNat 64 heap).toNat = heap := by decide
    rw [hheap]
    refine ⟨⟨(heap, heap + 0x10000), by simp [rt], Nat.le_refl _, by simp only [heap]; omega⟩,
      by simp only [heap]; omega, ?_, fun _ => by decide, fun _ _ => by decide, fun _ => ?_, hle⟩
    · rw [rtView_accessible] at hacc
      exact Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)
    · have := ZeroBytes.of_rtView hz ⟨(heap, heap + 0x10000), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩
      exact fun i hi => this i (by omega)

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def dsegs : List DataSegment := Extracted.data

def bytes (a : Nat) : Byte :=
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => BitVec.ofNat 8 ((Fv256.C.bigEntries.lookup a).getD 0)

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def zp : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigBase

def s0 : State :=
  { regs := fun i => if i = 0 then zp else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 4144, 4168, true⟩, ⟨g0, 0x100, false⟩, ⟨heap, 0x10000, true⟩, ⟨0x30800, 0x100, false⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [zp] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH : H [byteType, 0, 32] (s0.regs 28).toNat (s0.sp.toNat - 48) (rtView rt s0.mem) := by
  have hpt : byteType = tyA := by unfold tyA; decide
  rw [hpt]
  have hbase : ∀ d ∈ dsegs, 0x20000 ≤ d.base := by simp only [dsegs]; decide
  refine ⟨tyA, 0, 32, rfl, ⟨(tyA, tyA + 16), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩, by decide, by decide, ?_⟩
  intro i hi
  show (if _ then bytes (heap + i) else 0) = 0
  split
  · have h1 : dsegs.find? (fun d => decide (d.base ≤ heap + i ∧ heap + i < d.base + d.bytes.length)) = none := by
      rw [List.find?_eq_none]
      intro d hd
      have := hbase d hd
      have hh : heap + i < 0x20000 := by simp only [heap]; omega
      simp only [decide_eq_true_eq]
      omega
    simp only [bytes, h1]
    have h2 : Fv256.C.bigEntries.lookup (heap + i) = none := Fv256.C.bigEntries_none _ (by simp only [heap]; omega)
    rw [h2]; rfl
  · rfl

set_option maxRecDepth 100000 in
theorem pre : GuardOK s0 0 ∧ StackOK s0 4144 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 4144) 4168 rt ∧ Ptr32 s0.mem zp false ∧ Outside zp.toNat 32 rt ∧
    Disjoint zp.toNat 32 (s0.sp.toNat - 4144) 4168 ∧
    H [byteType, 0, 32] (s0.regs 28).toNat (s0.sp.toNat - 48) (rtView rt s0.mem) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, outside_cons, outside_nil]; decide, ⟨by decide, by decide⟩,
    by simp only [rt, outside_cons, outside_nil]; decide, by unfold Disjoint; decide, hH⟩

-- CALLSITE-BLOCK lean/Fv256/Arm64/CallSites/MarshalSSZ.lean
def csMk0 : State := { s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else if i = 1 then 0#64 else if i = 2 then 32#64 else s0.regs i }
/-- The call state of `runtime.makeslice` (U-WITNESS-CALLSITE): `makeslice(uint8, 0, 32)` at its entry in the caller's frame (`SP = sp0 - 48`, as in `hH`). -/
def csMk : State := { csMk0 with sp := BitVec.ofNat 64 (sp0 - 48), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") }

set_option maxRecDepth 100000 in
theorem csMk_pre : MakesliceSite H rt 4096 csMk := by
  refine ⟨⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    typeOK_of (by decide) (by decide), by decide, by decide, by decide⟩, ?_⟩
  have e0 : (csMk.regs 0).toNat = byteType := by
    have hpt : byteType = tyA := by unfold tyA; decide
    rw [hpt]; decide
  have e1 : (csMk.regs 1).toNat = 0 := by decide
  have e2 : (csMk.regs 2).toNat = 32 := by decide
  have e3 : (csMk.regs 28).toNat = (s0.regs 28).toNat := by decide
  have e4 : csMk.sp.toNat = s0.sp.toNat - 48 := by decide
  show H [(csMk.regs 0).toNat, (csMk.regs 1).toNat, (csMk.regs 2).toNat] (csMk.regs 28).toNat csMk.sp.toNat (rtView rt csMk.mem)
  rw [e0, e1, e2, e3, e4]
  exact hH

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `rt`, `H`), the contract hypotheses, an admissible
return address, a call state and the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (ret : Nat) (s : State),
    MakesliceContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧ Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧
        Disjoint z.toNat 32 (s.sp.toNat - 4144) 4168 ∧
        H [byteType, 0, 32] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem)) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧ MakesliceSite H rt 4096 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 1).toNat = 32 ∧ (s'.regs 2).toNat = 32 ∧
        s'.regs 3 = 0 ∧ s'.regs 4 = 0 ∧ InRanges ptr 32 rt ∧ s'.mem.accessible ptr 32 true = true ∧
        s'.mem.readLE ptr 32 = val256 s.mem z.toNat ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]) :=
  ⟨impl, rt, H, zp, ret, s0, hmk, hret, setup, pre,
    ⟨csMk, rfl, csMk_pre⟩,
    correctness_proof impl rt H zp hmk ret hret s0 setup pre⟩
end Wit

end Fv256.Arm64.MarshalSSZ
