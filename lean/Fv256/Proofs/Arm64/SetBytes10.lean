import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).SetBytes10(in []byte) *Int` (arm64)

**Guarantee.** For every receiver `z` (`X0`) and slice `in = (ptr, len, cap)` (`X1`-`X3`), every Go call whose stack-growth
check falls through (`GuardOK s 0`) and whose stack window `[SP-24, SP+24)` is writable and aligned (`StackOK s 24 24`):
if `len ≥ 10`, the 32 bytes at `z` are writable, the 10 bytes at `ptr` are readable, and neither overlaps the other or the
stack window, then the call returns (no fault, no panic), obeys the ABI, returns `z` in `X0`, the number at `z` afterwards is
`Fv256.Spec.fromBE` of the first 10 bytes of the slice (the big-endian reading, bytes read before the call), and no byte
changes outside `z[0..32)` and the stack window (`Fv256.Util.OnlyWrites2`).
If `len < 10` the call reaches the bounds-check panic stub (`Panics`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the preconditions; `Witness.returns`: it returns.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SetBytes10

theorem core (z ptr len cap : BitVec 64) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s)
    (hg : GuardOK s 0) (hst : StackOK s 24 24) :
    ((10 ≤ len.toNat → Ptr32 s.mem z true → Ptr s.mem ptr 10 false →
      Disjoint z.toNat 32 ptr.toNat 10 → Disjoint z.toNat 32 (s.sp.toNat - 24) 48 → Disjoint ptr.toNat 10 (s.sp.toNat - 24) 48 →
      Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + i) 1) 10 ∧
          Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 24) 48))) ∧
    (len.toNat < 10 → Ptr32 s.mem z true → Panics (Extracted.program.withExit ret) s) := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  janus_intro hs
  refine ⟨?_, fun hl => ?_⟩
  · intro hl ⟨hz, hz'⟩ ⟨hp, hp'⟩ hd1 hd2 hd3
    simp only [Disjoint] at hd1 hd2 hd3
    janus_run
    refine ⟨?_, ?_⟩
    · have := Util.rd1_lt s.mem (ptr.toNat); have := Util.rd1_lt s.mem (ptr.toNat + 1); have := Util.rd1_lt s.mem (ptr.toNat + 2); have := Util.rd1_lt s.mem (ptr.toNat + 3); have := Util.rd1_lt s.mem (ptr.toNat + 4); have := Util.rd1_lt s.mem (ptr.toNat + 5); have := Util.rd1_lt s.mem (ptr.toNat + 6); have := Util.rd1_lt s.mem (ptr.toNat + 7); have := Util.rd1_lt s.mem (ptr.toNat + 8); have := Util.rd1_lt s.mem (ptr.toNat + 9); (try simp only [Util.chunk8, Util.chunk4, Util.chunk2, Util.chunk2n, Util.rot0]); all_goals (simp only [Spec.fromBE, Nat.add_zero, Nat.reducePow, Nat.reduceAdd, Nat.add_assoc, Nat.zero_add]; (try simp (disch := omega) only [Util.or_hi16, Util.or_hi24, Util.or_hi32, Util.or_hi40, Util.or_hi48, Util.or_hi56, Nat.mod_eq_of_lt]); (try omega))
    · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]
  · intro ⟨_hzw, _hzw'⟩
    janus_run

theorem correctness (z ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, ptr, len, cap]
      (fun s => GuardOK s 0 ∧ StackOK s 24 24 ∧ 10 ≤ len.toNat ∧ Ptr32 s.mem z true ∧ Ptr s.mem ptr 10 false ∧
        Disjoint z.toNat 32 ptr.toNat 10 ∧ Disjoint z.toNat 32 (s.sp.toNat - 24) 48 ∧
        Disjoint ptr.toNat 10 (s.sp.toNat - 24) 48)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + i) 1) 10 ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 24) 48) := by
  intro ret hret s hs ⟨hg, hst, hl, h1, h2, h3, h4, h5⟩
  exact (core z ptr len cap ret hret s hs hg hst).1 hl h1 h2 h3 h4 h5

/-- The bounds check: with fewer than 10 bytes the call reaches the panic stub. -/
theorem panics (z ptr len cap : BitVec 64) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s)
    (hg : GuardOK s 0) (hst : StackOK s 24 24) :
    len.toNat < 10 → Ptr32 s.mem z true → Panics (Extracted.program.withExit ret) s :=
  (core z ptr len cap ret hret s hs hg hst).2

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def ptr : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then ptr else if i = 2 then 10 else if i = 3 then 10
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, 10, 10] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

theorem hg : GuardOK s0 0 := by unfold GuardOK; decide
theorem hst : StackOK s0 24 24 := by unfold StackOK; decide

theorem hpre : 10 ≤ (10 : BitVec 64).toNat ∧ Ptr32 s0.mem z true ∧ Ptr s0.mem ptr 10 false ∧
    Disjoint z.toNat 32 ptr.toNat 10 ∧ Disjoint z.toNat 32 (s0.sp.toNat - 24) 48 ∧
    Disjoint ptr.toNat 10 (s0.sp.toNat - 24) 48 := by
  refine ⟨by decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_⟩ <;> (unfold Disjoint; decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z ptr len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s ∧
    (GuardOK s 0 ∧ StackOK s 24 24 ∧ 10 ≤ len.toNat ∧ Ptr32 s.mem z true ∧ Ptr s.mem ptr 10 false ∧
      Disjoint z.toNat 32 ptr.toNat 10 ∧ Disjoint z.toNat 32 (s.sp.toNat - 24) 48 ∧
      Disjoint ptr.toNat 10 (s.sp.toNat - 24) 48) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + i) 1) 10 ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 24) 48 := by
  refine ⟨ret, s0, z, ptr, 10, 10, hret, setup, ?w2,
    correctness z ptr 10 10 ret hret s0 setup ?w2⟩
  case w2 => exact ⟨hg, hst, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧
      val256 s'.mem z.toNat = Fv256.Spec.fromBE (fun i => s0.mem.readLE (ptr.toNat + i) 1) 10 ∧
      Fv256.Util.OnlyWrites2 s0.mem s'.mem z.toNat 32 (s0.sp.toNat - 24) 48 :=
  (core z ptr 10 10 ret hret s0 setup hg hst).1 hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2.1 hpre.2.2.2.2.2

end Witness

end Fv256.Arm64.SetBytes10
