import Extracted
import Fv256.Proofs.Arm64.CallSites.Base
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Spec.Arm64.NewInt

/-!
# `uint256.NewInt(val uint64) *Int` (arm64)

**Guarantee.** For every `val` (`X0`), every list `rt` of runtime-owned memory ranges and **every** implementation of
`runtime.newobject` satisfying the allocation contract (`NewobjectContract`, `Janus/Contracts/Alloc.lean`; hypothesis `hnew`),
and every Go call whose stack-growth check falls through (`GuardOK s 0`, the stack window `[SP-4144, SP+24)` (NewInt's frame, 4096 bytes for the runtime, spill slots) writable and aligned (`StackOK s 4144 24`)) outside `rt`, with the read-only data (the type descriptor of `Int`) loaded,
the call returns, obeys the ABI, and the result is a pointer `ptr`
with `[ptr, ptr+32)` inside the runtime-owned ranges (a *fresh* object, disjoint from everything the caller holds), writable and
16-byte aligned, whose 32 bytes hold `Fv256.Spec.setU val` (the number `val`; the allocator returns zeroed memory), and memory is unchanged outside `rt` and the stack window.

**What is assumed.** Only the contract hypothesis `hnew` for the code linked at `runtime.newobject` (not extracted: `janus extract --contract
runtime.newobject`); see `docs/RUNTIME-CONTRACTS.md` of Janus.

**Non-vacuity.** `Witness.nonvacuous` / `Witness.returns`: a toy allocator (two instructions, returning a fixed zeroed heap) is linked at the `runtime.newobject` address, its contract `hnew` is proved by symbolic execution, and a concrete call state satisfies every precondition, so the hypotheses are jointly satisfiable and the theorem fires (the call returns a fresh object in `rt` holding the expected value).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.NewInt

set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (val : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [val]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧
        H [intType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
        s'.mem.accessible ptr 32 true = true ∧ val256 s'.mem ptr = Spec.setU val.toNat ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, hH⟩
  janus_intro hs
  janus_eval_nat h_pt : intType
  rw [h_pt] at hH
  janus_data hd [hw]
  janus_run until [Extracted.entry + 0x28] calls [hnew.pos]
  have hdj := InRanges.disjoint ‹InRanges _ 32 rt› hout
  janus_run
  refine ⟨_, rfl, ‹_›, ‹_›, ‹_›, ?_, ?_⟩
  · have hzb := ‹ZeroBytes _ _ 32›
    have z8 := hzb.readLE (k := 8) (j := 8) (by omega)
    have z16 := hzb.readLE (k := 16) (j := 8) (by omega)
    have z24 := hzb.readLE (k := 24) (j := 8) (by omega)
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]
    rw [z8, z16, z24]
    have := val.isLt
    simp only [Spec.setU]
    omega
  · janus_frame

namespace Witness

open Janus.Contracts.IfaceModel

def heap : Nat := 0x10000
def tyA : Nat := janus_eval% intType
def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def rt : List (Nat × Nat) := [(heap, heap + 0x10000), (tyA, tyA + 16)]

/-- A toy allocator at the runtime.newobject address: `MOVZ X0, #1, LSL #16; RET` (returns the heap at `0x10000`). -/
def impl : List Segment :=
  [{ name := "witness.newobject", base := cA, words := [0xd2a00020, 0xd65f03c0] }]

def H : RtReady := fun args _ _ v =>
  ∃ typ, args = [typ] ∧ InRanges typ 16 rt ∧ typSize v typ ≤ 32768 ∧
    v.accessible heap 0x10000 true = true ∧ ZeroBytes v heap 0x10000

def linked : Program := Extracted.program.link impl

theorem addr : Extracted.program.contractAddr "runtime.newobject" = cA := by decide

theorem callRegs_eq (r : Nat → W64) :
    callRegs r r [BitVec.ofNat 64 heap] = setReg r 0 (BitVec.ofNat 64 heap) := by
  funext i
  simp only [callRegs, setReg]
  rcases i with _ | i
  · rfl
  · simp only [List.getD_cons_succ, List.getD_nil]
    split <;> rfl

theorem hnew : NewobjectContract (Extracted.program.link impl)
    (Extracted.program.contractAddr "runtime.newobject") rt 4096 H := by
  rw [addr]
  intro s hpc ⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩, typ, hargs, hin, hsz, hacc, hz⟩
  simp only [List.cons.injEq, and_true] at hargs
  subst hargs
  change ReachesRet linked _ s _
  janus_run
  refine ⟨BitVec.ofNat 64 heap, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_, ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩,
    fun hpos => ?_⟩
  · simp only [retStateX]; rw [callRegs_eq]; rfl
  · unfold typSize at hsz
    rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
    change typSize s.mem (s.regs 0).toNat ≤ 32768 at hsz
    have hb := blockSize_le_maxSmallSize (typSize s.mem (s.regs 0).toNat)
      (typNoscan s.mem (s.regs 0).toNat) hsz
    have hle : typSize s.mem (s.regs 0).toNat ≤
        blockSize (typSize s.mem (s.regs 0).toNat) (typNoscan s.mem (s.regs 0).toNat) := by
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
def zp : Nat := 0x30800
def dat : DataSegment := Extracted.data.head!
def dlen : Nat := janus_eval% dat.bytes.length

def bytes (a : Nat) : Byte :=
  if tyA ≤ a ∧ a < tyA + dlen then BitVec.ofNat 8 (dat.bytes.getD (a - tyA) 0) else 0

def arg : BitVec 64 := 5#64

def s0 : State :=
  { regs := fun i => if i = 0 then arg else if i = 28 then BitVec.ofNat 64 g0
      else if i = 29 then BitVec.ofNat 64 sp0 - 8#64 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 4144, 4168, true⟩, ⟨g0, 0x100, false⟩, ⟨tyA, dlen, false⟩,
      ⟨heap, 0x10000, true⟩, ⟨zp, 0x100, false⟩]⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [arg] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH : H [intType] (s0.regs 28).toNat (s0.sp.toNat - 48) (rtView rt s0.mem) := by
  have hpt : intType = tyA := by unfold tyA; decide
  rw [hpt]
  refine ⟨tyA, rfl, ⟨(tyA, tyA + 16), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩, by decide,
    by decide, ?_⟩
  intro i hi
  have h1 : ¬(tyA ≤ heap + i ∧ heap + i < tyA + dlen) := by
    simp only [tyA, heap, dlen]; omega
  show (if _ then bytes (heap + i) else 0) = 0
  split
  · simp only [bytes]; rw [if_neg h1]
  · rfl

theorem pre : GuardOK s0 0 ∧ StackOK s0 4144 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 4144) 4168 rt ∧
    H [intType] (s0.regs 28).toNat (s0.sp.toNat - 48) (rtView rt s0.mem) :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, outside_cons, outside_nil]; decide, hH⟩

-- CALLSITE-BLOCK lean/Fv256/Arm64/CallSites/NewInt.lean
def wsNew0 : State := { s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else s0.regs i }
/-- The call state of `runtime.newobject` (U-WITNESS-CALLSITE): at the allocator's entry, `X0 = Int`'s type descriptor, `SP` = the frame
of the caller (the argument of `H` in `hH`), `X28`/memory as in `s0`. -/
def wsNew : State := { wsNew0 with sp := BitVec.ofNat 64 (sp0 - 48), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") }

set_option maxRecDepth 100000 in
theorem wsNew_pre : NewobjectSite H rt 4096 wsNew := by
  refine ⟨⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    typeOK_of (by decide) (by decide), by decide⟩, ?_⟩
  have e0 : (wsNew.regs 0).toNat = intType := by
    have hpt : intType = tyA := by unfold tyA; decide
    rw [hpt]; decide
  have e1 : (wsNew.regs 28).toNat = (s0.regs 28).toNat := by decide
  have e2 : wsNew.sp.toNat = s0.sp.toNat - 48 := by decide
  show H [(wsNew.regs 0).toNat] (wsNew.regs 28).toNat wsNew.sp.toNat (rtView rt wsNew.mem)
  rw [e0, e1, e2]
  exact hH

/-- The preconditions and the allocator contract are jointly satisfiable: a concrete call state (with the toy allocator linked at
the `runtime.newobject` address) meets every hypothesis of `correctness`. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State) (z : BitVec 64),
    NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4144) 4168 rt ∧
    H [intType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem)) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectSite H rt 4096 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
        s'.mem.accessible ptr 32 true = true ∧ val256 s'.mem ptr = Spec.setU z.toNat ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]) :=
  ⟨impl, rt, H, ret, s0, arg, hnew, hret, setup, pre,
    ⟨wsNew, rfl, wsNew_pre⟩,
    correctness impl rt H arg hnew ret hret s0 setup pre⟩



/-- The theorem fires: for this call and this allocator, `NewInt` returns a fresh object in `rt` holding the expected value. -/
theorem returns : Returns (linked.withExit ret) s0 (fun s' => ABIReturn s0 s' ∧
    ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
        s'.mem.accessible ptr 32 true = true ∧ val256 s'.mem ptr = Spec.setU arg.toNat ∧
        MemFrame s0.mem s'.mem (rt ++ [(s0.sp.toNat - 4144, s0.sp.toNat + 24)])) :=
  correctness impl rt H arg hnew ret hret s0 setup pre

end Witness

end Fv256.Arm64.NewInt
