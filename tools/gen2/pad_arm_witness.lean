namespace Witness

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
  { regs := fun i => if i = 0 then zp else if i = 1 then 5#64 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 4144, 4168, true⟩, ⟨g0, 0x100, false⟩, ⟨heap, 0x10000, true⟩, ⟨0x30800, 0x100, false⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [zp, 5#64] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH : H [byteType, 5, 5] (s0.regs 28).toNat (s0.sp.toNat - 48) (rtView rt s0.mem) := by
  have hpt : byteType = tyA := by unfold tyA; decide
  rw [hpt]
  have hbase : ∀ d ∈ dsegs, 0x20000 ≤ d.base := by simp only [dsegs]; decide
  refine ⟨tyA, 5, 5, rfl, ⟨(tyA, tyA + 16), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩, by decide, by decide, ?_⟩
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
    H [byteType, 5, 5] (s0.regs 28).toNat (s0.sp.toNat - 48) (rtView rt s0.mem) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, outside_cons, outside_nil]; decide, ⟨by decide, by decide⟩,
    by simp only [rt, outside_cons, outside_nil]; decide, by unfold Disjoint; decide, hH⟩

theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State) (z n : BitVec 64),
    MakesliceContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, n] s ∧
    n.toNat ≤ 2 ^ 48 ∧
    (GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4144) 4168 rt ∧ Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧
    Disjoint z.toNat 32 (s.sp.toNat - 4144) 4168 ∧
    H [byteType, n.toNat, n.toNat] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem)) :=
  ⟨impl, rt, H, ret, s0, zp, 5, hmk, hret, setup, (by decide), pre⟩


/-- The theorem fires: for `n = 5` the call returns a slice of length and capacity 5 inside a fresh object. -/
theorem returns : Returns (linked.withExit ret) s0 (fun s' => ABIReturn s0 s' ∧ (s'.regs 1).toNat = 5 ∧ (s'.regs 2).toNat = 5) := by
  refine (correctness impl rt H zp 5#64 (by decide) hmk ret hret s0 setup pre).mono ?_
  intro s' ⟨hab, ptr, _, h1, h2, _⟩
  exact ⟨hab, h1, h2⟩

end Witness

end Fv256.Arm64.PaddedBytes
