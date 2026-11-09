import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Spec.Amd64.Or

/-!
# `(*uint256.Int).Or(x, y) *Int` (amd64): `z = x ||| y`

**Guarantee.** For all pointers `z`, `x`, `y` and every Go call state with them in `RAX` (receiver), `RBX`, `RCX` such that
the return-address slot is writable, the 32 bytes at `z` are writable and those at `x`, `y` readable (below `2^48`),
`z` does not overlap the return-address slot, and every pair of the three pointers is equal or disjoint, the call
returns (no fault, no panic), obeys the ABI, returns `z` in `RAX`, the number at `z` afterwards is `Fv256.Spec.or` of
the numbers at `x` and `y` before the call, and no byte outside `z[0..32)` changes.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z` with value `0`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Or

theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧
        Disjoint z 32 (s.regs regSP) 8 ∧ Alias z x ∧ Alias z y ∧ Alias x y)
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.or (valueAt s x 32) (valueAt s y 32) ∧
        Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨_, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, hds, hzx, hzy, hxy⟩
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw hds
  simp only [valueAt, Spec.or, Disjoint, Alias] at *
  rcases hzx with rfl | hzx <;> rcases hzy with rfl | hzy <;> rcases hxy with h | hxy
  all_goals try subst h
  all_goals first | (exfalso; omega) | (janus64_run [Util.readLE_32]; rw [Util.or4 _ _ _ _ _ _ _ _ (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _)]; simp [Util.or_mod_rd, Nat.or_comm]; all_goals simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self])

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

theorem hpre : StackWritable s0 0 8 ∧ Buffer s0 z 32 true ∧ Buffer s0 x 32 false ∧ Buffer s0 x 32 false ∧
    Disjoint z 32 (s0.regs regSP) 8 ∧ Alias z x ∧ Alias z x ∧ Alias x x :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    by unfold Disjoint; decide, Or.inr (by unfold Disjoint; decide), Or.inr (by unfold Disjoint; decide), Or.inl rfl⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧
    (StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧
      Disjoint z 32 (s.regs regSP) 8 ∧ Alias z x ∧ Alias z y ∧ Alias x y) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.or (valueAt s x 32) (valueAt s y 32) ∧
        Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32 :=
  ⟨ret, s0, z, x, x, hret, setup, hpre,
    correctness z x x ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ valueAt s' z 32 = 0 := by
  refine (correctness z x x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  simp only [valueAt, Spec.or]
  decide

end Witness

end Fv256.Amd64.Or
