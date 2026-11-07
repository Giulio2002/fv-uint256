import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).Mul(x, y) *Int` (amd64): `z = x * y`

**Guarantee.** For all pointers `z`, `x`, `y` (any overlap between them is allowed: every input limb is loaded before the first store) and every Go call state with them in `RAX` (receiver), `RBX`, `RCX` such that
the return-address slot is writable, the 32 bytes at `z` are writable and those at `x`, `y` readable (below `2^48`),
`z` does not overlap the return-address slot, the call
returns (no fault, no panic), obeys the ABI, returns `z` in `RAX`, the number at `z` afterwards is `Fv256.Spec.mul` of
the numbers at `x` and `y` before the call, and no byte changes outside `z[0..32)` and the callee's 16-byte scratch slot just below the stack pointer (`Fv256.Util.OnlyWrites2`). The three operands are also assumed not to overlap that scratch slot or the return-address slot.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z` with value `0`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Mul

/-- equal or disjoint 32-byte objects -/
def Alias (p q : BitVec 64) : Prop := p = q ∨ Disjoint p 32 q 32

theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => StackWritable s 16 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 16 ∨ (s.regs regSP).toNat + 8 ≤ z.toNat) ∧ (x.toNat + 32 ≤ (s.regs regSP).toNat - 16 ∨ (s.regs regSP).toNat ≤ x.toNat) ∧ (y.toNat + 32 ≤ (s.regs regSP).toNat - 16 ∨ (s.regs regSP).toNat ≤ y.toNat))
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.mul (valueAt s x 32) (valueAt s y 32) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 16) 16) := by
  intro ret hret s hs ⟨⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, hds, hdx, hdy⟩
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw hds hlow hdx hdy
  simp only [valueAt, Spec.mul, Disjoint, Alias] at *
  all_goals first | (exfalso; omega) | (janus64_run [Util.readLE_32]; all_goals ((try have := Util.readLE8_lt s.mem (z.toNat )); (try have := Util.readLE8_lt s.mem (z.toNat + 8)); (try have := Util.readLE8_lt s.mem (z.toNat + 16)); (try have := Util.readLE8_lt s.mem (z.toNat + 24)); (try have := Util.readLE8_lt s.mem (x.toNat )); (try have := Util.readLE8_lt s.mem (x.toNat + 8)); (try have := Util.readLE8_lt s.mem (x.toNat + 16)); (try have := Util.readLE8_lt s.mem (x.toNat + 24)); (try have := Util.readLE8_lt s.mem (y.toNat )); (try have := Util.readLE8_lt s.mem (y.toNat + 8)); (try have := Util.readLE8_lt s.mem (y.toNat + 16)); (try have := Util.readLE8_lt s.mem (y.toNat + 24)); refine ⟨?_, ?_⟩; (· simp only [Spec.mul, Spec.W, Nat.reducePow, BitVec.toNat_mul, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reduceMod]; janus64_arith); (· simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff])))

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then x else if i = 1 then x
      else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackWritable s0 16 8 ∧ Buffer s0 z 32 true ∧ Buffer s0 x 32 false ∧ Buffer s0 x 32 false ∧
    (z.toNat + 32 ≤ (s0.regs regSP).toNat - 16 ∨ (s0.regs regSP).toNat + 8 ≤ z.toNat) ∧ (x.toNat + 32 ≤ (s0.regs regSP).toNat - 16 ∨ (s0.regs regSP).toNat ≤ x.toNat) ∧ (x.toNat + 32 ≤ (s0.regs regSP).toNat - 16 ∨ (s0.regs regSP).toNat ≤ x.toNat) :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    by decide, by decide, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧
    (StackWritable s 16 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧
      (z.toNat + 32 ≤ (s.regs regSP).toNat - 16 ∨ (s.regs regSP).toNat + 8 ≤ z.toNat) ∧ (x.toNat + 32 ≤ (s.regs regSP).toNat - 16 ∨ (s.regs regSP).toNat ≤ x.toNat) ∧ (y.toNat + 32 ≤ (s.regs regSP).toNat - 16 ∨ (s.regs regSP).toNat ≤ y.toNat)) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.mul (valueAt s x 32) (valueAt s y 32) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 16) 16 :=
  ⟨ret, s0, z, x, x, hret, setup, hpre,
    correctness z x x ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ valueAt s' z 32 = 0 := by
  refine (correctness z x x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  simp only [valueAt, Spec.mul]
  decide

end Witness

end Fv256.Amd64.Mul
