import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Amd64.MoCases.A
import Fv256.Proofs.Amd64.MoCases.B
import Fv256.Proofs.Amd64.MoCases.C
import Fv256.Proofs.Amd64.MoCases.D
import Fv256.Proofs.Amd64.MoCases.E
import Fv256.Spec.Amd64.MulOverflow

/-!
# `(*uint256.Int).MulOverflow(x, y *Int) (*Int, bool)` (amd64): `z = x * y mod 2^256` and the overflow flag

**Guarantee.** For all pointers `z`, `x`, `y` (`RAX`, `RBX`, `RCX`) with the 32 bytes at `z` writable and those at `x`, `y` readable (below `2^48`),
every pair of the three pointers equal or disjoint, the 168-byte window around the stack pointer (`StackWritable s 152 16`: the function's frame and
the extracted `umul` callee's) disjoint from the three objects, `RSP` 8-aligned, and a Go call whose stack check falls through (`StackGuardOK s 0`):
the call returns (no fault, no panic), obeys the ABI, returns `z` in `RAX`, the overflow flag in `RBX` (low byte) is `1` iff `x*y >= 2^256`, the number at `z`
afterwards is `Fv256.Spec.mul` of the numbers at `x` and `y` before the call, and no byte changes outside `z[0..32)` and the stack window.
One proof module per aliasing pattern of `(z, x, y)` (`MoCases/A..E`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MulOverflow

set_option maxHeartbeats 64000000 in
theorem correctness_proof (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 152 16 ∧ (s.regs regSP).toNat % 8 = 0 ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Alias z x ∧ Alias z y ∧ Alias x y ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 152 ∨ (s.regs regSP).toNat + 16 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 152 ∨ (s.regs regSP).toNat + 16 ≤ x.toNat) ∧
        (y.toNat + 32 ≤ (s.regs regSP).toNat - 152 ∨ (s.regs regSP).toNat + 16 ≤ y.toNat))
      (fun s s' => s'.regs 0 = z ∧
        (s'.regs 3).toNat % 256 = (if Spec.W ≤ valueAt s x 32 * valueAt s y 32 then 1 else 0) ∧
        valueAt s' z 32 = Spec.mul (valueAt s x 32) (valueAt s y 32) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 152) 168) := by
  intro ret hret s hs ⟨hg, hst, hal, hz, hx, hy, hzx, hzy, hxy, hd1, hd2, hd3⟩
  rcases hzx with hzx | hzx
  · subst hzx
    rcases hzy with hzy | hzy
    · subst hzy
      exact caseE _ ret hret s hs ⟨hg, hst, hal, hz, hx, hy, hd1⟩
    · exact caseB _ _ ret hret s hs ⟨hg, hst, hal, hz, hx, hy, hzy, hd1, hd3⟩
  · rcases hzy with hzy | hzy
    · subst hzy
      exact caseC _ _ ret hret s hs ⟨hg, hst, hal, hz, hx, hy, hzx, hd1, hd2⟩
    · rcases hxy with hxy | hxy
      · subst hxy
        exact caseD _ _ ret hret s hs ⟨hg, hst, hal, hz, hx, hy, hzx, hd1, hd2⟩
      · exact caseA _ _ _ ret hret s hs ⟨hg, hst, hal, hz, hx, hy, hzx, hzy, hxy, hd1, hd2, hd3⟩

namespace Wit

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def zp : Nat := 0x30800

/-- the return address in the slot at `[SP]`, everything else zero -/
def bytes (a : Nat) : Byte := if a = sp0 + 2 then 0x20 else 0

def z : BitVec 64 := BitVec.ofNat 64 zp
def x : BitVec 64 := BitVec.ofNat 64 (zp + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then x else if i = 1 then x else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 152, 152 + 16, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, true⟩]⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : StackGuardOK s0 0 ∧ StackWritable s0 152 16 ∧ (s0.regs regSP).toNat % 8 = 0 ∧
    Buffer s0 z 32 true ∧ Buffer s0 x 32 false ∧ Buffer s0 x 32 false ∧ Alias z x ∧ Alias z x ∧ Alias x x ∧
    (z.toNat + 32 ≤ (s0.regs regSP).toNat - 152 ∨ (s0.regs regSP).toNat + 16 ≤ z.toNat) ∧
    (x.toNat + 32 ≤ (s0.regs regSP).toNat - 152 ∨ (s0.regs regSP).toNat + 16 ≤ x.toNat) ∧
    (x.toNat + 32 ≤ (s0.regs regSP).toNat - 152 ∨ (s0.regs regSP).toNat + 16 ≤ x.toNat) :=
  ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩, ⟨by decide, by decide, by decide⟩, by decide,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, Or.inr (Or.inl (by decide)), Or.inr (Or.inl (by decide)), Or.inl rfl,
    by decide, by decide, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 152 16 ∧ (s.regs regSP).toNat % 8 = 0 ∧
      Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Alias z x ∧ Alias z y ∧ Alias x y ∧
      (z.toNat + 32 ≤ (s.regs regSP).toNat - 152 ∨ (s.regs regSP).toNat + 16 ≤ z.toNat) ∧
      (x.toNat + 32 ≤ (s.regs regSP).toNat - 152 ∨ (s.regs regSP).toNat + 16 ≤ x.toNat) ∧
      (y.toNat + 32 ≤ (s.regs regSP).toNat - 152 ∨ (s.regs regSP).toNat + 16 ≤ y.toNat)) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        (s'.regs 3).toNat % 256 = (if Spec.W ≤ valueAt s x 32 * valueAt s y 32 then 1 else 0) ∧
        valueAt s' z 32 = Spec.mul (valueAt s x 32) (valueAt s y 32) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 152) 168 :=
  ⟨ret, s0, z, x, x, hret, setup, hpre,
    correctness_proof z x x ret hret s0 setup hpre⟩

set_option maxRecDepth 100000 in
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ (s'.regs 3).toNat % 256 = 0 ∧ valueAt s' z 32 = 0 := by
  refine (correctness_proof z x x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · rw [h.2.2.1]; unfold valueAt; decide
  · rw [h.2.2.2.1]; unfold valueAt Spec.mul; decide

end Wit

end Fv256.Amd64.MulOverflow
