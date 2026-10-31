import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC

/-!
# `(*uint256.Int).UnmarshalSSZ(buf []byte) error` (arm64) -- PARTIAL: the success path (`len(buf) = 32`)

**Scope.** For `len(buf) ≠ 32` the function builds an error with `fmt.Errorf("%w: have %d, want %d bytes", ErrBadEncodedLength, ...)`;
`fmt.errorf` (and `runtime.convT64`, `runtime.newobject` on that path) are left out of the extraction (`--contract`) and this
theorem says nothing about that path (COVERAGE-C.md: partial).

**Guarantee.** For every receiver `z` and slice `buf = (bp, 32, cap)` with 32 readable bytes at `bp`, 32 writable bytes at `z`, disjoint from
each other and from the stack window: the call returns a nil error and the number at `z` is the little-endian reading of the 32 bytes
(read before the call); nothing else changes except the stack frame.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.UnmarshalSSZ

set_option maxHeartbeats 16000000 in
theorem correctness (z bp len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, bp, len, cap]
      (fun s => GuardOK s 0 ∧ StackOK s 120 24 ∧ len.toNat = 32 ∧ Ptr32 s.mem z true ∧ Ptr32 s.mem bp false ∧
        Disjoint z.toNat 32 bp.toNat 32 ∧ Disjoint z.toNat 32 (s.sp.toNat - 120) 144 ∧
        Disjoint bp.toNat 32 (s.sp.toNat - 120) 144 ∧ s.regs 29 = s.sp - 8#64)
      (fun s s' => s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ val256 s'.mem z.toNat = s.mem.readLE bp.toNat 32 ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat + 16, s.sp.toNat + 24), (s.sp.toNat - 120, s.sp.toNat)]) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hl, ⟨hz, hz'⟩, ⟨hp, hp'⟩, hd1, hd2, hd3, hfp⟩
  janus_intro hs
  simp only [Disjoint] at hd1 hd2 hd3
  janus_run
  refine ⟨Fv256.C.ofNat_sub8 _ (Nat.le_trans (by decide) hb), ?_, ?_⟩
  · rw [Util.readLE_32 s.mem bp.toNat]
  · janus_frame

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def bp : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then bp else if i = 2 then 32 else if i = 3 then 32
      else if i = 28 then BitVec.ofNat 64 wg else if i = 29 then BitVec.ofNat 64 wsp - 8#64
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, bp, 32, 32] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

theorem hpre : GuardOK s0 0 ∧ StackOK s0 120 24 ∧ (32 : BitVec 64).toNat = 32 ∧ Ptr32 s0.mem z true ∧ Ptr32 s0.mem bp false ∧
    Disjoint z.toNat 32 bp.toNat 32 ∧ Disjoint z.toNat 32 (s0.sp.toNat - 120) 144 ∧
    Disjoint bp.toNat 32 (s0.sp.toNat - 120) 144 ∧ s0.regs 29 = s0.sp - 8#64 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, by decide, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ?_, ?_, ?_, rfl⟩ <;> (unfold Disjoint; decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z bp len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, bp, len, cap] s ∧
    (GuardOK s 0 ∧ StackOK s 120 24 ∧ len.toNat = 32 ∧ Ptr32 s.mem z true ∧ Ptr32 s.mem bp false ∧
      Disjoint z.toNat 32 bp.toNat 32 ∧ Disjoint z.toNat 32 (s.sp.toNat - 120) 144 ∧
      Disjoint bp.toNat 32 (s.sp.toNat - 120) 144 ∧ s.regs 29 = s.sp - 8#64) :=
  ⟨ret, s0, z, bp, 32, 32, hret, setup, hpre⟩

/-- the call returns a nil error and writes the little-endian reading of the 32 bytes at `bp` into `z`. -/
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ val256 s'.mem z.toNat = s0.mem.readLE bp.toNat 32 :=
  (fun h => h.mono fun s' h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) (correctness z bp 32 32 ret hret s0 setup hpre)

end Witness

end Fv256.Arm64.UnmarshalSSZ
