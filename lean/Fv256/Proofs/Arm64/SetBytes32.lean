import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).SetBytes32(in []byte) *Int` (arm64)

**Guarantee.** For every receiver `z` (`X0`) and slice `in = (ptr, len, cap)` (`X1`-`X3`), every Go call whose stack-growth
check falls through (`GuardOK s 0`) and whose stack window `[SP-24, SP+24)` is writable and aligned (`StackOK s 24 24`):
if `len ≥ 32`, the 32 bytes at `z` are writable, the 32 bytes at `ptr` are readable, and neither overlaps the other or the
stack window, then the call returns (no fault, no panic), obeys the ABI, returns `z` in `X0`, the number at `z` afterwards is
`Fv256.Spec.fromBE` of the first 32 bytes of the slice (the big-endian reading, bytes read before the call), and no byte
changes outside `z[0..32)` and the stack window (`Fv256.Util.OnlyWrites2`).
If `len < 32` the call reaches the bounds-check panic stub (`Panics`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the preconditions; `Witness.returns`: it returns.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SetBytes32

theorem core (z ptr len cap : BitVec 64) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s)
    (hg : GuardOK s 0) (hst : StackOK s 24 24) :
    ((32 ≤ len.toNat → Ptr32 s.mem z true → Ptr s.mem ptr 32 false →
      Disjoint z.toNat 32 ptr.toNat 32 → Disjoint z.toNat 32 (s.sp.toNat - 24) 48 → Disjoint ptr.toNat 32 (s.sp.toNat - 24) 48 →
      Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + i) 1) 32 ∧
          Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 24) 48))) ∧
    (len.toNat < 32 → Panics (Extracted.program.withExit ret) s) := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  janus_intro hs
  refine ⟨?_, fun hl => ?_⟩
  · intro hl ⟨hz, hz'⟩ ⟨hp, hp'⟩ hd1 hd2 hd3
    simp only [Disjoint] at hd1 hd2 hd3
    janus_run
    refine ⟨?_, ?_⟩
    · rw [Util.be32_rev]
      rw [Util.rc_rev8 _ (Util.readLE8_lt _ _), Util.rc_rev8 _ (Util.readLE8_lt _ _), Util.rc_rev8 _ (Util.readLE8_lt _ _), Util.rc_rev8 _ (Util.readLE8_lt _ _)]
      omega
    · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]
  · janus_run

theorem correctness (z ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, ptr, len, cap]
      (fun s => GuardOK s 0 ∧ StackOK s 24 24 ∧ 32 ≤ len.toNat ∧ Ptr32 s.mem z true ∧ Ptr s.mem ptr 32 false ∧
        Disjoint z.toNat 32 ptr.toNat 32 ∧ Disjoint z.toNat 32 (s.sp.toNat - 24) 48 ∧
        Disjoint ptr.toNat 32 (s.sp.toNat - 24) 48)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + i) 1) 32 ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 24) 48) := by
  intro ret hret s hs ⟨hg, hst, hl, h1, h2, h3, h4, h5⟩
  exact (core z ptr len cap ret hret s hs hg hst).1 hl h1 h2 h3 h4 h5

/-- The bounds check: with fewer than 32 bytes the call reaches the panic stub. -/
theorem panics (z ptr len cap : BitVec 64) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s)
    (hg : GuardOK s 0) (hst : StackOK s 24 24) :
    len.toNat < 32 → Ptr32 s.mem z true → Panics (Extracted.program.withExit ret) s :=
  fun hl _ => (core z ptr len cap ret hret s hs hg hst).2 hl

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def ptr : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then ptr else if i = 2 then 32 else if i = 3 then 32
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, 32, 32] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

theorem hg : GuardOK s0 0 := by unfold GuardOK; decide
theorem hst : StackOK s0 24 24 := by unfold StackOK; decide

theorem hpre : 32 ≤ (32 : BitVec 64).toNat ∧ Ptr32 s0.mem z true ∧ Ptr s0.mem ptr 32 false ∧
    Disjoint z.toNat 32 ptr.toNat 32 ∧ Disjoint z.toNat 32 (s0.sp.toNat - 24) 48 ∧
    Disjoint ptr.toNat 32 (s0.sp.toNat - 24) 48 := by
  refine ⟨by decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_⟩ <;> (unfold Disjoint; decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z ptr len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s ∧
    (GuardOK s 0 ∧ StackOK s 24 24 ∧ 32 ≤ len.toNat ∧ Ptr32 s.mem z true ∧ Ptr s.mem ptr 32 false ∧
      Disjoint z.toNat 32 ptr.toNat 32 ∧ Disjoint z.toNat 32 (s.sp.toNat - 24) 48 ∧
      Disjoint ptr.toNat 32 (s.sp.toNat - 24) 48) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + i) 1) 32 ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 24) 48 := by
  refine ⟨ret, s0, z, ptr, 32, 32, hret, setup, ?w2,
    correctness z ptr 32 32 ret hret s0 setup ?w2⟩
  case w2 => exact ⟨hg, hst, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧
      val256 s'.mem z.toNat = Fv256.Spec.fromBE (fun i => s0.mem.readLE (ptr.toNat + i) 1) 32 ∧
      Fv256.Util.OnlyWrites2 s0.mem s'.mem z.toNat 32 (s0.sp.toNat - 24) 48 :=
  (core z ptr 32 32 ret hret s0 setup hg hst).1 hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2

end Witness

end Fv256.Arm64.SetBytes32
