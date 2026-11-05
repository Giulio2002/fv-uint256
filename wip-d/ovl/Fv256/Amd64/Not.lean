import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).Not(x *Int) *Int` (amd64): `z = Fv256.Spec.not x`

**Guarantee.** For all pointers `z` (receiver, `RAX`) and `x` (`RBX`) and every Go call state such that the return-address slot
is writable, the 32 bytes at `z` are writable, those at `x` readable (below `2^48`), `z` does not overlap the return-address
slot, and `z`, `x` are equal or disjoint, the call returns (no fault, no panic), obeys the ABI, returns `z` in `RAX`, the number
at `z` afterwards is `Fv256.Spec.not` of the number at `x` before the call, and no byte outside `z[0..32)` changes.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z` holding `Spec.not 0`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Not

/-- equal or disjoint 32-byte objects -/
def Alias (p q : BitVec 64) : Prop := p = q ∨ Disjoint p 32 q 32

theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x]
      (fun s => StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
        Disjoint z 32 (s.regs regSP) 8 ∧ Alias z x)
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.not (valueAt s x 32) ∧
        Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨_, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, hds, hzx⟩
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw hds
  simp only [valueAt, Disjoint, Alias] at *
  rcases hzx with rfl | hzx
  all_goals first | (exfalso; omega) | (janus64_run [Util.readLE_32]; all_goals (refine ⟨?_, ?_⟩; (· (try have := Util.readLE8_lt s.mem (z.toNat )); (try have := Util.readLE8_lt s.mem (z.toNat + 8)); (try have := Util.readLE8_lt s.mem (z.toNat + 16)); (try have := Util.readLE8_lt s.mem (z.toNat + 24)); (try have := Util.readLE8_lt s.mem (x.toNat )); (try have := Util.readLE8_lt s.mem (x.toNat + 8)); (try have := Util.readLE8_lt s.mem (x.toNat + 16)); (try have := Util.readLE8_lt s.mem (x.toNat + 24)); (try have := Util.readLE8_lt s.mem (y.toNat )); (try have := Util.readLE8_lt s.mem (y.toNat + 8)); (try have := Util.readLE8_lt s.mem (y.toNat + 16)); (try have := Util.readLE8_lt s.mem (y.toNat + 24)); simp only [BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Spec.not, Spec.W]; omega); (· simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self])))

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then x else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackWritable s0 0 8 ∧ Buffer s0 z 32 true ∧ Buffer s0 x 32 false ∧
    Disjoint z 32 (s0.regs regSP) 8 ∧ Alias z x :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    by unfold Disjoint; decide, Or.inr (by unfold Disjoint; decide)⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧
    (StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
      Disjoint z 32 (s.regs regSP) 8 ∧ Alias z x) :=
  ⟨ret, s0, z, x, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ valueAt s' z 32 = Spec.not 0 := by
  refine (correctness z x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  simp only [valueAt]
  decide

end Witness

end Fv256.Amd64.Not
