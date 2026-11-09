import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).SRsh(x *Int, n uint) *Int` (amd64): arithmetic shift right, `z = x >> n` (sign-propagating)

**Guarantee.** For all pointers `z` (receiver, `RAX`) and `x` (`RBX`), shift count `n` (`RCX`, any 64-bit value) and every Go call whose
stack-growth check falls through (`StackGuardOK s 0`) and whose stack window `[RSP-40, RSP+8)` is writable (`StackWritable s 40 8`):
if the 32 bytes at `z` are writable, those at `x` readable (below `2^48`), `z` and `x` are equal or disjoint, and neither overlaps the
stack window, then the call returns (no fault, no panic), obeys the ABI, returns `z` in `RAX`, the number at `z` afterwards is
`Fv256.Spec.srsh` of the number at `x` before the call (the two's-complement reading of `x` shifted right by `n` with sign fill, i.e.
`~(~x >> n)` for negative `x`; counts of 256 or more give 0 or all ones), and no byte outside `z[0..32)` and the stack window changes (`Fv256.Util.OnlyWrites2`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z` holding the result.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SRsh

/-- equal or disjoint 32-byte objects -/
def Alias (p q : BitVec 64) : Prop := p = q ∨ Disjoint p 32 q 32

set_option maxHeartbeats 16000000 in
theorem correctness (z x n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, n]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 40 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat + 8 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧ Alias z x)
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.srsh (valueAt s x 32) n.toNat ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 40) 48) := by
  intro ret hret s hs ⟨hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, hds, hdsx, hzx⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hlow hacc hnw hds hdsx
  simp only [valueAt, Disjoint, Alias] at *
  rcases hzx with rfl | hzx
  · @@Z@@  · @@X@@

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)
def n : BitVec 64 := 0#64

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then x else if i = 1 then n else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, n] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackGuardOK s0 0 ∧ StackWritable s0 40 8 ∧ Buffer s0 z 32 true ∧ Buffer s0 x 32 false ∧
    (z.toNat + 32 ≤ (s0.regs regSP).toNat - 40 ∨ (s0.regs regSP).toNat + 8 ≤ z.toNat) ∧
    (x.toNat + 32 ≤ (s0.regs regSP).toNat - 40 ∨ (s0.regs regSP).toNat + 8 ≤ x.toNat) ∧ Alias z x :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    by decide, by decide, Or.inr (by unfold Disjoint; decide)⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, n] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 40 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
      (z.toNat + 32 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat + 8 ≤ z.toNat) ∧
      (x.toNat + 32 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧ Alias z x) :=
  ⟨ret, s0, z, x, n, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ valueAt s' z 32 = 0 := by
  refine (correctness z x n ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  simp only [valueAt]
  decide

end Witness

end Fv256.Amd64.SRsh
