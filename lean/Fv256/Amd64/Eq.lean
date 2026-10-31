import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).Eq(x *Int) bool` (amd64)

**Guarantee.** For all pointers `z` (receiver, `RAX`) and `x` (`RBX`) such that the return-address slot is writable and
the 32 bytes at each are readable (below `2^48`; they may be equal or overlap arbitrarily) the call returns (no fault,
no panic), obeys the ABI, and the `bool` result is `Fv256.Spec.eq` of the number at the receiver and the number at `x` (`AL`, low byte of `RAX`), the numbers being read before the call.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `1`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Eq

theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x]
      (fun s => StackWritable s 0 8 ∧ Buffer s z 32 false ∧ Buffer s x 32 false)
      (fun s s' => (s'.regs 0).toNat % 256 = (Spec.eq (valueAt s z 32) (valueAt s x 32)).toNat) := by
  intro ret hret s hs ⟨⟨_, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩⟩
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  simp only [valueAt]
  janus64_run [Util.readLE_32]
  all_goals (have := Util.readLE8_lt s.mem (z.toNat ); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat ); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); simp only [Spec.eq, Util.beq_toNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; (repeat' split) <;> first | omega | (simp; omega) | simp_all)

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

theorem hpre : StackWritable s0 0 8 ∧ Buffer s0 z 32 false ∧ Buffer s0 x 32 false :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧
    (StackWritable s 0 8 ∧ Buffer s z 32 false ∧ Buffer s x 32 false) :=
  ⟨ret, s0, z, x, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat % 256 = 1 := by
  refine (correctness z x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [valueAt]
  decide

end Witness

end Fv256.Amd64.Eq
