import Extracted
import Fv256.Proofs.Arm64.ErlpDefs

/-!
# `EncodeRLP` non-vacuity witness material (arm64): a toy `runtime.newobject` and a toy `io.Writer.Write`

`mov x0, x2 ; mov x1, xzr ; mov x2, xzr ; ret` is the writer (`(len, nil)`), reached through the itab word `tab+24`.
The value at `z` is `0x011234`, a 17-bit number: the multi-byte path.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

set_option linter.unusedSimpArgs false

namespace Fv256.Arm64.EncodeRLP.Witness

open Janus.Contracts.IfaceModel

def heap : Nat := 0x10000
def tyA : Nat := janus_eval% tyBig
def tyB : Nat := janus_eval% tyOne
def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
abbrev A0 : Nat := 0x700000
def rt : List (Nat × Nat) := [(heap, heap + 0x10000), (tyA, tyA + 16), (tyB, tyB + 16)]
def stack : Nat := 4104

def impl : List Segment :=
  [{ name := "witness.newobject", base := cA, words := [0xd2a00020, 0xd65f03c0] },
   { name := "witness.writer", base := A0, words := [0xaa0203e0, 0xaa1f03e1, 0xaa1f03e2, 0xd65f03c0] }]

def H : RtReady := fun args _ _ v =>
  ∃ typ, args = [typ] ∧ InRanges typ 16 rt ∧ typSize v typ ≤ 32768 ∧
    v.accessible heap 0x10000 true = true ∧ ZeroBytes v heap 0x10000

/-- the writer's relation: it returns `(len, nil)` -/
def R0 : Res := fun _ _ a2 _ n e1 e2 => n = a2 ∧ e1 = 0 ∧ e2 = 0

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

/-- the abstract writer's return state -/
theorem wret_of {st : Nat} (s : State) (R : Nat → W64) (F : Flags) (h0 : R 0 = s.regs 2) (h1 : R 1 = 0) (h2 : R 2 = 0)
    (h18 : R 18 = s.regs 18) (h28 : R 28 = s.regs 28) (h29 : R 29 = s.regs 29) (hF : F = s.flags) :
    ICallRetP 4 st rt (fun _ => []) R0 (fun _ _ => True) s { s with regs := R, flags := F, pc := s.regs 30 } := by
  refine ⟨R, F, s.vregs, s.mem, s.excl, s.exclPass, ?_, MemFrame.refl _ _, by simp, ?_⟩
  · simp only [retStateX]
    congr 1
    funext i
    simp only [callRegs]
    by_cases h : i = 18 ∨ i = 28 ∨ i = 29
    · rcases h with rfl | rfl | rfl <;> simp [h18, h28, h29]
    · simp only [h, ite_false, List.getD_nil]
  · exact ⟨⟨h0, h1, h2⟩, trivial⟩

theorem hw (z w : BitVec 64) : ICallContract (Extracted.program.link impl) A0 4 stack 96 rt (fun _ => []) R0 (WP z w) := by
  intro s hpc ⟨⟨hr1, hr2, _⟩, _⟩
  have hpc' : s.pc = 0x700000#64 := hpc
  change ReachesRet linked _ s _
  janus_run [hpc']
  all_goals
    apply wret_of
    all_goals simp [setReg]

def retA : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def zp : Nat := 0x30800
def tabp : Nat := 0x31000
def dsegs : List DataSegment := Extracted.data

/-- the memory: the zeroed heap, `*z = 0x011234` (a 17-bit number), the itab word `tab+24 = A0`, the data objects -/
def bytes (a : Nat) : Byte :=
  if heap ≤ a ∧ a < heap + 0x10000 then 0 else
  if a = zp then 0x34 else if a = zp + 1 then 0x12 else if a = zp + 2 then 0x01 else
  if a = tabp + 26 then 0x70 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def zA : BitVec 64 := BitVec.ofNat 64 zp
def tabA : BitVec 64 := BitVec.ofNat 64 tabp
def wA : BitVec 64 := 0x777

def s0 : State :=
  { regs := fun i => if i = 0 then zA else if i = 1 then tabA else if i = 2 then wA else if i = 28 then BitVec.ofNat 64 g0
      else if i = 29 then BitVec.ofNat 64 sp0 - 8#64 else if i = 30 then BitVec.ofNat 64 retA else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 4168, 4200, true⟩, ⟨g0, 0x100, false⟩, ⟨heap, 0x10000, true⟩, ⟨zp, 0x100, false⟩,
      ⟨tabp, 0x100, false⟩] ++ dregs⟩ }

set_option maxRecDepth 100000 in
theorem hret : RetAddr linked retA := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit retA) Extracted.entry [zA, tabA, wA] s0 :=
  ⟨rfl, rfl, by
    intro i h
    match i, h with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH (ty : Nat) (hty : ty = tyA ∨ ty = tyB) :
    H [ty] (s0.regs 28).toNat (s0.sp.toNat - 64) (rtView rt s0.mem) := by
  refine ⟨ty, rfl, ?_, ?_, by rw [rtView_accessible]; decide, fun i hi => ?_⟩
  · rcases hty with rfl | rfl
    · exact ⟨(tyA, tyA + 16), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(tyB, tyB + 16), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩
  · rcases hty with rfl | rfl <;> decide
  · show (if _ then bytes (heap + i) else 0) = 0
    split
    · have hh : heap = 65536 := rfl
      simp only [bytes]
      rw [if_pos (show heap ≤ heap + i ∧ heap + i < heap + 0x10000 from ⟨by omega, by omega⟩)]
    · rfl

set_option maxRecDepth 100000 in
theorem pre : 4104 ≤ stack ∧ CodePtrOK A0 ∧ GuardOK s0 0 ∧ StackOK s0 (64 + stack) 32 ∧
    Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 64 - stack) (stack + 96) rt ∧
    (zA = 0 ∨ (Ptr32 s0.mem zA false ∧ Outside zA.toNat 32 rt ∧
      Disjoint zA.toNat 32 (s0.sp.toNat - 64 - stack) (stack + 96))) ∧
    Disjoint (tabA.toNat + 24) 8 (s0.sp.toNat - 64 - stack) (stack + 96) ∧
    tabA.toNat + 32 ≤ 2 ^ 48 ∧ s0.mem.accessible (tabA.toNat + 24) 8 false = true ∧ Outside (tabA.toNat + 24) 8 rt ∧
    s0.mem.readLE (tabA.toNat + 24) 8 = A0 ∧
    H [tyBig] (s0.regs 28).toNat (s0.sp.toNat - 64) (rtView rt s0.mem) ∧
    H [tyOne] (s0.regs 28).toNat (s0.sp.toNat - 64) (rtView rt s0.mem) :=
  ⟨by decide, ⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, outside_cons, outside_nil]; decide,
    Or.inr ⟨⟨by decide, by decide⟩, by simp only [rt, outside_cons, outside_nil]; decide, by unfold Disjoint; decide⟩,
    by unfold Disjoint; decide, by decide, by decide, by simp only [rt, outside_cons, outside_nil]; decide, by decide,
    hH tyBig (Or.inl rfl), hH tyOne (Or.inr rfl)⟩

end Fv256.Arm64.EncodeRLP.Witness
