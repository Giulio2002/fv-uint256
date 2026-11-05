namespace Witness

open Janus.Contracts.AllocSatAmd64 (ret_of)
open Janus.Contracts.AllocSat (le_blockSize)

def heap : Nat := 0x10000
def tyA : Nat := janus_eval% byteType
def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.makeslice")
def rt : List (Nat × Nat) := [(heap, heap + 0x10000), (tyA, tyA + 16)]

def impl : List Janus.Amd64.Segment :=
  [{ name := "witness.makeslice", base := cA, bytes := [0xb8, 0x00, 0x00, 0x01, 0x00, 0xc3] }]

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
  { regs := fun i => if i = 0 then zp else if i = 3 then 5 else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 4136, 4136 + 24, true⟩, ⟨g0, 0x100, false⟩, ⟨heap, 0x10000, true⟩, ⟨0x30800, 0x100, false⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [zp, 5] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Janus.Amd64.Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH : H [byteType, (5 : BitVec 64).toNat, (5 : BitVec 64).toNat] (s0.regs 14).toNat ((s0.regs 4).toNat - 40) (rtView rt s0.mem) := by
  have hpt : byteType = tyA := by unfold tyA; decide
  rw [hpt]
  have hbase : ∀ d ∈ dsegs, 0x20000 ≤ d.base := by simp only [dsegs]; decide
  refine ⟨⟨by rw [rtView_accessible]; decide, fun i hi => ?_⟩, tyA, 5, 5, rfl,
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
    H [byteType, (5 : BitVec 64).toNat, (5 : BitVec 64).toNat] (s0.regs 14).toNat ((s0.regs 4).toNat - 40) (rtView rt s0.mem) := by
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, outside_cons, outside_nil]; decide, by decide, ⟨by decide, by decide⟩,
    by simp only [rt, outside_cons, outside_nil]; decide, by decide, hH⟩

/-- The preconditions and the allocator contract are jointly satisfiable: a concrete call state (with the toy allocator linked at
the `runtime.makeslice` address) meets every hypothesis of `correctness`, for `n = 5`. -/
theorem nonvacuous : CallSetup (linked.withExit ret) Extracted.entry [zp, 5] s0 ∧
    (StackGuardOK s0 0 ∧ StackWritable s0 4136 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 4).toNat - 4136) 4160 rt ∧ (s0.regs 4).toNat % 8 = 0 ∧
    Buffer s0 zp 32 false ∧ Outside zp.toNat 32 rt ∧
    (zp.toNat + 32 ≤ (s0.regs 4).toNat - 4136 ∨ (s0.regs 4).toNat + 24 ≤ zp.toNat) ∧
    H [byteType, (5 : BitVec 64).toNat, (5 : BitVec 64).toNat] (s0.regs 14).toNat ((s0.regs 4).toNat - 40) (rtView rt s0.mem)) :=
  And.intro setup pre

/-- The theorem fires: for this call and this allocator, `PaddedBytes(5)` returns a fresh 5-byte slice in `rt`. -/
example := correctness impl rt H zp 5 (by decide) hmk ret hret s0 setup pre

end Witness
