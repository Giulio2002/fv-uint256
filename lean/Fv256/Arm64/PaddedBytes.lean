import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.Arm64.PadDefs
import Fv256.Arm64.PadCases.Case0
import Fv256.Arm64.PadCases.Case1
import Fv256.Arm64.PadCases.Case2
import Fv256.Arm64.PadCases.Case3
import Fv256.Arm64.PadCases.Case4
import Fv256.Arm64.PadCases.Case5
import Fv256.Arm64.PadCases.Case6
import Fv256.Arm64.PadCases.Case7
import Fv256.Arm64.PadCases.Case8
import Fv256.Arm64.PadCases.Case9
import Fv256.Arm64.PadCases.Case10
import Fv256.Arm64.PadCases.Case11
import Fv256.Arm64.PadCases.Case12
import Fv256.Arm64.PadCases.Case13
import Fv256.Arm64.PadCases.Case14
import Fv256.Arm64.PadCases.Case15
import Fv256.Arm64.PadCases.Case16
import Fv256.Arm64.PadCases.Case17
import Fv256.Arm64.PadCases.Case18
import Fv256.Arm64.PadCases.Case19
import Fv256.Arm64.PadCases.Case20
import Fv256.Arm64.PadCases.Case21
import Fv256.Arm64.PadCases.Case22
import Fv256.Arm64.PadCases.Case23
import Fv256.Arm64.PadCases.Case24
import Fv256.Arm64.PadCases.Case25
import Fv256.Arm64.PadCases.Case26
import Fv256.Arm64.PadCases.Case27
import Fv256.Arm64.PadCases.Case28
import Fv256.Arm64.PadCases.Case29
import Fv256.Arm64.PadCases.Case30
import Fv256.Arm64.PadCases.Case31
import Fv256.Arm64.PadCases.CaseBig

/-!
# `(*uint256.Int).PaddedBytes(n int) []byte` (arm64)

**Guarantee.** For every receiver `z` (`X0`), every `n` (`X1`) with `n <= 2^48` (the `runtime.makeslice` panic paths, negative or oversized
`n`, are excluded), every list `rt` of runtime-owned ranges and **every** implementation of `runtime.makeslice` meeting the pinned
allocation contract (`MakesliceContract`, hypothesis `hmk`), and every Go call whose stack check falls through (stack window
`[SP-4144, SP+24)` writable, aligned, outside `rt`), with the 32 bytes at `z` readable, outside `rt` and the stack window: the call
returns the slice `(ptr, n, n)`; for `n > 0`, `[ptr, ptr+n)` is a fresh object inside `rt` (writable), and its `n` bytes read big-endian
(`Fv256.Spec.fromBE`) as the number at `z` modulo `2^(8n)` (so zero padding on the left for `n > 32`, truncation of the high bytes for `n < 32`);
memory is unchanged outside `rt` and the stack window. The loop is unrolled: one proof module per `n = 0..31` and one for `n >= 32`.

**What is assumed.** Only the contract hypothesis `hmk` for the code linked at `runtime.makeslice` (not extracted).

**Non-vacuity.** `Witness.nonvacuous` / `Witness.returns`: a toy allocator at the `makeslice` address; for `n = 5` the call returns a slice of length and capacity 5.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.PaddedBytes

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z n : BitVec 64) (hn : n.toNat ≤ 2 ^ 48)
    (hmk : MakesliceContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, n]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧ Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧
        Disjoint z.toNat 32 (s.sp.toNat - 4144) 4168 ∧
        H [byteType, n.toNat, n.toNat] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 1).toNat = n.toNat ∧ (s'.regs 2).toNat = n.toNat ∧
        (0 < n.toNat → InRanges ptr n.toNat rt ∧ s'.mem.accessible ptr n.toNat true = true) ∧
        Spec.fromBE (fun i => s'.mem.readLE (ptr + i) 1) n.toNat = val256 s.mem z.toNat % 2 ^ (8 * n.toNat) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) := by
  intro ret hret s hs hpre
  by_cases h32 : 32 ≤ n.toNat
  · exact (caseBig impl rt H z n h32 hn hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
      ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
  · rcases (show n.toNat = 0 ∨ n.toNat = 1 ∨ n.toNat = 2 ∨ n.toNat = 3 ∨ n.toNat = 4 ∨ n.toNat = 5 ∨ n.toNat = 6 ∨ n.toNat = 7 ∨ n.toNat = 8 ∨ n.toNat = 9 ∨ n.toNat = 10 ∨ n.toNat = 11 ∨ n.toNat = 12 ∨ n.toNat = 13 ∨ n.toNat = 14 ∨ n.toNat = 15 ∨ n.toNat = 16 ∨ n.toNat = 17 ∨ n.toNat = 18 ∨ n.toNat = 19 ∨ n.toNat = 20 ∨ n.toNat = 21 ∨ n.toNat = 22 ∨ n.toNat = 23 ∨ n.toNat = 24 ∨ n.toNat = 25 ∨ n.toNat = 26 ∨ n.toNat = 27 ∨ n.toNat = 28 ∨ n.toNat = 29 ∨ n.toNat = 30 ∨ n.toNat = 31 by omega) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31
    · have e : n = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h0)
      subst e
      exact (case0 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, g⟩ =>
        ⟨hab, ptr, a, b, c, fun h => absurd h (by simp), by simp [Spec.fromBE, Nat.mod_one], g⟩
    · have e : n = 1#64 := BitVec.eq_of_toNat_eq (by simpa using h1)
      subst e
      exact (case1 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 2#64 := BitVec.eq_of_toNat_eq (by simpa using h2)
      subst e
      exact (case2 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 3#64 := BitVec.eq_of_toNat_eq (by simpa using h3)
      subst e
      exact (case3 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 4#64 := BitVec.eq_of_toNat_eq (by simpa using h4)
      subst e
      exact (case4 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 5#64 := BitVec.eq_of_toNat_eq (by simpa using h5)
      subst e
      exact (case5 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 6#64 := BitVec.eq_of_toNat_eq (by simpa using h6)
      subst e
      exact (case6 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 7#64 := BitVec.eq_of_toNat_eq (by simpa using h7)
      subst e
      exact (case7 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 8#64 := BitVec.eq_of_toNat_eq (by simpa using h8)
      subst e
      exact (case8 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 9#64 := BitVec.eq_of_toNat_eq (by simpa using h9)
      subst e
      exact (case9 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 10#64 := BitVec.eq_of_toNat_eq (by simpa using h10)
      subst e
      exact (case10 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 11#64 := BitVec.eq_of_toNat_eq (by simpa using h11)
      subst e
      exact (case11 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 12#64 := BitVec.eq_of_toNat_eq (by simpa using h12)
      subst e
      exact (case12 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 13#64 := BitVec.eq_of_toNat_eq (by simpa using h13)
      subst e
      exact (case13 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 14#64 := BitVec.eq_of_toNat_eq (by simpa using h14)
      subst e
      exact (case14 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 15#64 := BitVec.eq_of_toNat_eq (by simpa using h15)
      subst e
      exact (case15 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 16#64 := BitVec.eq_of_toNat_eq (by simpa using h16)
      subst e
      exact (case16 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 17#64 := BitVec.eq_of_toNat_eq (by simpa using h17)
      subst e
      exact (case17 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 18#64 := BitVec.eq_of_toNat_eq (by simpa using h18)
      subst e
      exact (case18 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 19#64 := BitVec.eq_of_toNat_eq (by simpa using h19)
      subst e
      exact (case19 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 20#64 := BitVec.eq_of_toNat_eq (by simpa using h20)
      subst e
      exact (case20 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 21#64 := BitVec.eq_of_toNat_eq (by simpa using h21)
      subst e
      exact (case21 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 22#64 := BitVec.eq_of_toNat_eq (by simpa using h22)
      subst e
      exact (case22 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 23#64 := BitVec.eq_of_toNat_eq (by simpa using h23)
      subst e
      exact (case23 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 24#64 := BitVec.eq_of_toNat_eq (by simpa using h24)
      subst e
      exact (case24 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 25#64 := BitVec.eq_of_toNat_eq (by simpa using h25)
      subst e
      exact (case25 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 26#64 := BitVec.eq_of_toNat_eq (by simpa using h26)
      subst e
      exact (case26 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 27#64 := BitVec.eq_of_toNat_eq (by simpa using h27)
      subst e
      exact (case27 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 28#64 := BitVec.eq_of_toNat_eq (by simpa using h28)
      subst e
      exact (case28 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 29#64 := BitVec.eq_of_toNat_eq (by simpa using h29)
      subst e
      exact (case29 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 30#64 := BitVec.eq_of_toNat_eq (by simpa using h30)
      subst e
      exact (case30 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩
    · have e : n = 31#64 := BitVec.eq_of_toNat_eq (by simpa using h31)
      subst e
      exact (case31 impl rt H z hmk ret hret s hs hpre).mono fun s' ⟨hab, ptr, a, b, c, d, e, f, g⟩ =>
        ⟨hab, ptr, a, b, c, fun _ => ⟨d, e⟩, f, g⟩

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
    H [byteType, n.toNat, n.toNat] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem)) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 1).toNat = n.toNat ∧ (s'.regs 2).toNat = n.toNat ∧
        (0 < n.toNat → InRanges ptr n.toNat rt ∧ s'.mem.accessible ptr n.toNat true = true) ∧
        Spec.fromBE (fun i => s'.mem.readLE (ptr + i) 1) n.toNat = val256 s.mem z.toNat % 2 ^ (8 * n.toNat) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]) :=
  ⟨impl, rt, H, ret, s0, zp, 5, hmk, hret, setup, (by decide), pre,
    correctness impl rt H zp 5 (by decide) hmk ret hret s0 setup pre⟩


/-- The theorem fires: for `n = 5` the call returns a slice of length and capacity 5 inside a fresh object. -/
theorem returns : Returns (linked.withExit ret) s0 (fun s' => ABIReturn s0 s' ∧ (s'.regs 1).toNat = 5 ∧ (s'.regs 2).toNat = 5) := by
  refine (correctness impl rt H zp 5#64 (by decide) hmk ret hret s0 setup pre).mono ?_
  intro s' ⟨hab, ptr, _, h1, h2, _⟩
  exact ⟨hab, h1, h2⟩

end Witness

end Fv256.Arm64.PaddedBytes
