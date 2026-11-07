import Fv256.Amd64.CallSites.Live
import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.Amd64.UdivremA
import Fv256.Amd64.UdivremK
import Fv256.Amd64.UdivremL
import Fv256.Amd64.UdivremM
import Fv256.Amd64.DivModB
import Janus.Contracts.AllocSatAmd64

/-!
# Non-vacuity witness for `Fv256.Amd64.DivMod.correctness` (parts)

A concrete allocator (`mov eax, 0x10000; ret` at `runtime.newobject`'s address), the runtime-owned ranges, the readiness
predicate and the proof that they meet `NewobjectContract64`; a concrete call state of `(*Int).DivMod` that satisfies the
precondition.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
open Janus.Contracts.AllocSatAmd64 (A0 heapCode ret_of)
open Janus.Contracts.AllocSat (heap tyA HeapReady fresh_heap le_blockSize)

namespace Fv256.Amd64.DivModW

/-- The allocator, placed at `runtime.newobject`'s address in the extraction. -/
def cA : Nat := Extracted.program.contractAddr "runtime.newobject"

theorem cA_eq : cA = 0x41d9c0 := by decide

def impl : List Amd64.Segment := [{ name := "model", base := cA, bytes := heapCode }]

/-- `uint256.Int`'s type descriptor (the extraction's only data object). -/
def intTy : Nat := Extracted.dataAddr.«type:uint256.Int#33f34945»

/-- The runtime-owned ranges: the heap and `Int`'s type descriptor. -/
def rtW : List (Nat × Nat) := [(heap, heap + 0x10000), (intTy, intTy + 16)]

/-- Readiness: the heap is writable and zero and the argument is a type descriptor of at most 32 KiB inside `rtW`. -/
def HW : RtReady := fun args _ _ v =>
  HeapReady v ∧ ∃ typ, args = [typ] ∧ InRanges typ 16 rtW ∧ typSize v typ ≤ 32768


/-- The linked program, as one closed constant. -/
def linked : Amd64.Program := Extracted.program.link impl

/-- The object the toy allocator returns is `Fresh` for a request of at most 32 KiB. -/
theorem fresh_heapW {m : Janus.Arm64.Memory} {size round : Nat} (zero hdr : Bool)
    (hr : HeapReady (rtView rtW m)) (hsz : size ≤ round) (hround : round ≤ 32768) :
    Fresh rtW m heap size round zero hdr := by
  obtain ⟨hacc, hz⟩ := hr
  rw [rtView_accessible] at hacc
  have hz' := ZeroBytes.of_rtView hz ⟨(heap, heap + 0x10000), by simp [rtW], Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨⟨(heap, heap + 0x10000), by simp [rtW], Nat.le_refl _, by simp only [heap]; omega⟩,
    by simp only [heap]; omega, Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    fun _ => by decide, fun _ _ => by decide, fun _ => fun i hi => hz' i (by omega), hsz⟩

theorem hnewW : NewobjectContract64 linked cA rtW 4096 HW := by
  intro s hpc ⟨⟨⟨hra, hal, _, _, _⟩, _, _⟩, hr, typ, hargs, hin, hsz⟩
  simp only [List.cons.injEq, and_true] at hargs
  subst hargs
  janus64_run
  refine ⟨BitVec.ofNat 64 heap, _, _, _, _, _, _, _, ret_of s _ [BitVec.ofNat 64 heap]
    (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF, heap]) (by simp) (by simp) rfl rfl rfl rfl rfl,
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
  unfold typSize at hsz
  rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
  change typSize s.mem (s.regs 0).toNat ≤ 32768 at hsz
  rw [show (BitVec.ofNat 64 heap).toNat = heap from rfl]
  exact fresh_heapW _ _ hr (le_blockSize _ _)
    (blockSize_le_maxSmallSize _ _ (by simp only [maxSmallSize]; exact hsz))


/-! ## The concrete call -/

def wsp : Nat := 0x200000
def wg : Nat := 0x300000
def zA : Nat := 0x500000
def xA : Nat := 0x500100
def yA : Nat := 0x500200
def mA : Nat := 0x500300
def retW : Nat := 0x1000

def zW : BitVec 64 := BitVec.ofNat 64 zA
def xW : BitVec 64 := BitVec.ofNat 64 xA
def yW : BitVec 64 := BitVec.ofNat 64 yA
def mW : BitVec 64 := BitVec.ofNat 64 mA

def dataByte (a : Nat) : Option Arm64.Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

theorem dataByte_none (a : Nat) (ha : a < 0x4cbe00) : dataByte a = none := by
  unfold dataByte
  have : Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) = none := by
    rw [List.find?_eq_none]
    intro d hd
    have h2 : 0x4cbe00 ≤ d.base := by
      have : ∀ d' ∈ Extracted.data, 0x4cbe00 ≤ d'.base := by decide
      exact this d hd
    simp only [Bool.not_eq_true, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    left; omega
  rw [this]

/-- The return address `retW = 0x1000` is at `[RSP]`; the read-only data is `Extracted.data`; everything else is zero. -/
def bytesW (a : Nat) : Arm64.Byte :=
  match dataByte a with
  | some v => v
  | none => if a = wsp + 1 then 0x10 else 0

def memW : Memory :=
  ⟨bytesW, [⟨wsp - 4256, 4256 + 0x28, true⟩, ⟨wg, 0x100, false⟩, ⟨heap, 0x10000, true⟩, ⟨zA, 32, true⟩, ⟨xA, 32, false⟩,
    ⟨yA, 32, false⟩, ⟨mA, 32, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then zW else if i = 3 then xW else if i = 1 then yW else if i = 7 then mW
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := memW }

theorem hretW : RetAddr linked retW := RetAddr.of_check (by decide)

theorem setupW : CallSetup (linked.withExit retW) Extracted.entry [zW, xW, yW, mW] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; match i, h with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoadedW : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
  decide

theorem heapReadyW : HeapReady (rtView rtW memW) := by
  refine ⟨by decide, fun i hi => ?_⟩
  show (if _ then memW.bytes (heap + i) else 0) = 0
  split
  · show bytesW (heap + i) = 0
    simp only [bytesW, dataByte_none (heap + i) (by simp only [heap]; omega)]
    rw [if_neg (by simp only [heap, wsp]; omega)]
  · rfl


set_option maxRecDepth 100000 in
theorem typSizeW : typSize (rtView rtW memW) intTy ≤ 32768 := by decide

set_option maxRecDepth 100000 in
/-- The whole precondition of `DivMod.correctness` holds for the witness call (`intType` is `intTy`). -/
theorem preW : StackGuardOK s0 0x198 ∧ StackWritable s0 4256 0x28 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 4).toNat - 4256) (4256 + 0x28) rtW ∧ (s0.regs 4).toNat % 8 = 0 ∧
    Buffer s0 zW 32 true ∧ Buffer s0 xW 32 false ∧ Buffer s0 yW 32 false ∧ Buffer s0 mW 32 true ∧
    Outside zW.toNat 32 rtW ∧ Outside xW.toNat 32 rtW ∧ Outside yW.toNat 32 rtW ∧ Outside mW.toNat 32 rtW ∧
    (zW.toNat + 32 ≤ (s0.regs 4).toNat - 4256 ∨ (s0.regs 4).toNat + 0x28 ≤ zW.toNat) ∧
    (xW.toNat + 32 ≤ (s0.regs 4).toNat - 4256 ∨ (s0.regs 4).toNat + 0x28 ≤ xW.toNat) ∧
    (yW.toNat + 32 ≤ (s0.regs 4).toNat - 4256 ∨ (s0.regs 4).toNat + 0x28 ≤ yW.toNat) ∧
    (mW.toNat + 32 ≤ (s0.regs 4).toNat - 4256 ∨ (s0.regs 4).toNat + 0x28 ≤ mW.toNat) ∧
    (zW = mW ∨ zW.toNat + 32 ≤ mW.toNat ∨ mW.toNat + 32 ≤ zW.toNat) ∧
    ((s0.regs 14).toNat + 24 ≤ (s0.regs 4).toNat - 4256 ∨ (s0.regs 4).toNat + 0x28 ≤ (s0.regs 14).toNat + 16) ∧
    Outside ((s0.regs 14).toNat + 16) 8 rtW ∧
    HW [intTy] (s0.regs 14).toNat ((s0.regs 4).toNat - 0xa0) (rtView rtW s0.mem) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, dataLoadedW, ?_, by decide,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, Or.inr (Or.inl (by decide)), by decide, ?_, ?_⟩
  · simp only [outside_cons, outside_nil, and_true, rtW]; decide
  · simp only [outside_cons, outside_nil, and_true, rtW]; decide
  · simp only [outside_cons, outside_nil, and_true, rtW]; decide
  · simp only [outside_cons, outside_nil, and_true, rtW]; decide
  · simp only [outside_cons, outside_nil, and_true, rtW]; decide
  · simp only [outside_cons, outside_nil, and_true, rtW]; decide
  · exact ⟨heapReadyW, intTy, rfl, ⟨(intTy, intTy + 16), by simp [rtW], Nat.le_refl _, Nat.le_refl _⟩, typSizeW⟩

open Fv256.CallSites

/-- The call state of `runtime.newobject` (U-WITNESS-CALLSITE): `s0`'s memory at the allocator's entry, `RSP` at the call frame
(`s0`'s `RSP` less `0xa0`), `RAX` the `uint256.Int` type descriptor. -/
def csNewW : Amd64.State :=
  { s0 with rip := BitVec.ofNat 64 cA, regs := fun i => if i = 0 then BitVec.ofNat 64 intTy else if i = 4 then s0.regs 4 - 0xa0#64 else s0.regs i }

theorem csNewW_rip : csNewW.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") := rfl

set_option maxRecDepth 100000 in
theorem csNewW_pre : NewobjectSite HW rtW 4096 csNewW := by
  have ht : (csNewW.regs 0).toNat = intTy := by decide
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  show HW [(csNewW.regs 0).toNat] _ _ (rtView rtW s0.mem)
  rw [ht]; exact preW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Fv256.Amd64.DivModW
