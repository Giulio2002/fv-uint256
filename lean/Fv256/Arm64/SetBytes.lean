import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.Arm64.SetBytesDefs
import Fv256.Arm64.SbCases.Case0
import Fv256.Arm64.SbCases.Case1
import Fv256.Arm64.SbCases.Case2
import Fv256.Arm64.SbCases.Case3
import Fv256.Arm64.SbCases.Case4
import Fv256.Arm64.SbCases.Case5
import Fv256.Arm64.SbCases.Case6
import Fv256.Arm64.SbCases.Case7
import Fv256.Arm64.SbCases.Case8
import Fv256.Arm64.SbCases.Case9
import Fv256.Arm64.SbCases.Case10
import Fv256.Arm64.SbCases.Case11
import Fv256.Arm64.SbCases.Case12
import Fv256.Arm64.SbCases.Case13
import Fv256.Arm64.SbCases.Case14
import Fv256.Arm64.SbCases.Case15
import Fv256.Arm64.SbCases.Case16
import Fv256.Arm64.SbCases.Case17
import Fv256.Arm64.SbCases.Case18
import Fv256.Arm64.SbCases.Case19
import Fv256.Arm64.SbCases.Case20
import Fv256.Arm64.SbCases.Case21
import Fv256.Arm64.SbCases.Case22
import Fv256.Arm64.SbCases.Case23
import Fv256.Arm64.SbCases.Case24
import Fv256.Arm64.SbCases.Case25
import Fv256.Arm64.SbCases.Case26
import Fv256.Arm64.SbCases.Case27
import Fv256.Arm64.SbCases.Case28
import Fv256.Arm64.SbCases.Case29
import Fv256.Arm64.SbCases.Case30
import Fv256.Arm64.SbCases.Case31
import Fv256.Arm64.SbCases.CaseBig

/-!
# `(*uint256.Int).SetBytes(buf []byte) *Int` (arm64)

**Documented behaviour.** "SetBytes interprets buf as the bytes of a big-endian unsigned integer, sets z to that value, and
returns z. If buf is larger than 32 bytes, the last 32 bytes is used."

**Guarantee.** For every receiver `z` (`X0`) and slice `buf = (ptr, len, cap)` (`X1`-`X3`) with `len ≤ cap < 2^48`, every Go call
whose stack-growth check falls through and whose stack window is writable and aligned, with the 32 bytes at `z` writable, the `len`
bytes at `ptr` readable, and `z` and the used bytes (`min len 32` of them, ending at `ptr + len`) disjoint from each other and from the
stack window: the call returns (no fault, no panic), returns `z` in `X0`, the number at `z` afterwards is `Fv256.Spec.fromBE` of the
last `min len 32` bytes of `buf`, and no byte outside `z[0..32)` and the stack window changes.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SetBytes

namespace Fv256.Arm64.SetBytes

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem correctness (z ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, ptr, len, cap]
      (fun s => GuardOK s 48 ∧ StackOK s 88 72 ∧ Extracted.program.DataLoaded s.mem ∧ len.toNat ≤ cap.toNat ∧
        cap.toNat < 2 ^ 48 ∧ Ptr32 s.mem z true ∧ Ptr s.mem ptr len.toNat false ∧
        Disjoint z.toNat 32 (ptr.toNat + len.toNat - used len.toNat) (used len.toNat) ∧
        Disjoint z.toNat 32 (s.sp.toNat - 88) 160 ∧
        Disjoint (ptr.toNat + len.toNat - used len.toNat) (used len.toNat) (s.sp.toNat - 88) 160 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 88) 160)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat =
          Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + len.toNat - used len.toNat + i) 1) (used len.toNat) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 88) 160) := by
  intro ret hret s hs hpre
  rcases (show len.toNat = 0 ∨ len.toNat = 1 ∨ len.toNat = 2 ∨ len.toNat = 3 ∨ len.toNat = 4 ∨ len.toNat = 5 ∨ len.toNat = 6 ∨ len.toNat = 7 ∨ len.toNat = 8 ∨ len.toNat = 9 ∨ len.toNat = 10 ∨ len.toNat = 11 ∨ len.toNat = 12 ∨ len.toNat = 13 ∨ len.toNat = 14 ∨ len.toNat = 15 ∨ len.toNat = 16 ∨ len.toNat = 17 ∨ len.toNat = 18 ∨ len.toNat = 19 ∨ len.toNat = 20 ∨ len.toNat = 21 ∨ len.toNat = 22 ∨ len.toNat = 23 ∨ len.toNat = 24 ∨ len.toNat = 25 ∨ len.toNat = 26 ∨ len.toNat = 27 ∨ len.toNat = 28 ∨ len.toNat = 29 ∨ len.toNat = 30 ∨ len.toNat = 31 ∨ 32 ≤ len.toNat by omega) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | hbig
  · have hl : len = BitVec.ofNat 64 0 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case0 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 1 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case1 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 2 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case2 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 3 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case3 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 4 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case4 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 5 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case5 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 6 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case6 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 7 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case7 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 8 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case8 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 9 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case9 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 10 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case10 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 11 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case11 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 12 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case12 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 13 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case13 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 14 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case14 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 15 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case15 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 16 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case16 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 17 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case17 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 18 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case18 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 19 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case19 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 20 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case20 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 21 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case21 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 22 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case22 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 23 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case23 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 24 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case24 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 25 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case25 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 26 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case26 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 27 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case27 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 28 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case28 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 29 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case29 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 30 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case30 z ptr cap ret hret s hs hpre
  · have hl : len = BitVec.ofNat 64 31 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    exact case31 z ptr cap ret hret s hs hpre
  · exact caseBig z ptr len cap hbig ret hret s hs hpre

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def zp : Nat := 0x30800
def dat : DataSegment := Extracted.data.head!
def dbase : Nat := janus_eval% dat.base
def dlen : Nat := janus_eval% dat.bytes.length

/-- the jump table is in memory (read-only data), everything else is zero -/
def bytes (a : Nat) : Byte :=
  if dbase ≤ a ∧ a < dbase + dlen then BitVec.ofNat 8 (dat.bytes.getD (a - dbase) 0) else 0

def z : BitVec 64 := BitVec.ofNat 64 zp
def ptr : BitVec 64 := BitVec.ofNat 64 (zp + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then ptr else if i = 2 then 10 else if i = 3 then 10
      else if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 88, 160, true⟩, ⟨g0, 0x100, false⟩, ⟨dbase, dlen, false⟩, ⟨zp, 0x200, true⟩]⟩ }

set_option maxRecDepth 100000 in
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, 10, 10] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : GuardOK s0 48 ∧ StackOK s0 88 72 ∧ Extracted.program.DataLoaded s0.mem ∧
    (10 : BitVec 64).toNat ≤ (10 : BitVec 64).toNat ∧ (10 : BitVec 64).toNat < 2 ^ 48 ∧ Ptr32 s0.mem z true ∧
    Ptr s0.mem ptr (10 : BitVec 64).toNat false ∧
    Disjoint z.toNat 32 (ptr.toNat + (10 : BitVec 64).toNat - used (10 : BitVec 64).toNat) (used (10 : BitVec 64).toNat) ∧
    Disjoint z.toNat 32 (s0.sp.toNat - 88) 160 ∧
    Disjoint (ptr.toNat + (10 : BitVec 64).toNat - used (10 : BitVec 64).toNat) (used (10 : BitVec 64).toNat) (s0.sp.toNat - 88) 160 ∧
    Disjoint ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 88) 160 := by
  refine ⟨by unfold GuardOK; decide, by unfold StackOK; decide, by unfold Program.DataLoaded; decide, by decide, by decide,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_, ?_⟩ <;> first | (unfold Disjoint used; decide) | (unfold Disjoint; decide) | (unfold used; decide) | decide

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z ptr len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s ∧
    (GuardOK s 48 ∧ StackOK s 88 72 ∧ Extracted.program.DataLoaded s.mem ∧ len.toNat ≤ cap.toNat ∧
      cap.toNat < 2 ^ 48 ∧ Ptr32 s.mem z true ∧ Ptr s.mem ptr len.toNat false ∧
      Disjoint z.toNat 32 (ptr.toNat + len.toNat - used len.toNat) (used len.toNat) ∧
      Disjoint z.toNat 32 (s.sp.toNat - 88) 160 ∧
      Disjoint (ptr.toNat + len.toNat - used len.toNat) (used len.toNat) (s.sp.toNat - 88) 160 ∧
      Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 88) 160) :=
  ⟨ret, s0, z, ptr, 10, 10, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧
      val256 s'.mem z.toNat =
        Spec.fromBE (fun i => s0.mem.readLE (ptr.toNat + (10 : BitVec 64).toNat - used (10 : BitVec 64).toNat + i) 1)
          (used (10 : BitVec 64).toNat) ∧
      Util.OnlyWrites2 s0.mem s'.mem z.toNat 32 (s0.sp.toNat - 88) 160 :=
  correctness z ptr 10 10 ret hret s0 setup hpre

end Witness

end Fv256.Arm64.SetBytes
