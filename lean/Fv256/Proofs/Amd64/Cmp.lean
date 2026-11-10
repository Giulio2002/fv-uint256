import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).Cmp(x *Int) int` (amd64)

**Guarantee.** For all pointers `z` (receiver, `RAX`) and `x` (`RBX`) such that the return-address slot is writable and
the 32 bytes at each are readable (below `2^48`; they may be equal or overlap arbitrarily) the call returns (no fault,
no panic), obeys the ABI, and the `int` result is `Fv256.Spec.cmp` of the number at the receiver and the number at `x` (`RAX`, read as a signed 64-bit integer: -1, 0 or 1), the numbers being read before the call.

**Non-vacuity.** `Wit.nonvacuous`: a concrete call satisfies the precondition; `Wit.returns`: it returns `0`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Cmp

set_option maxHeartbeats 8000000 in
theorem correctness_proof (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x]
      (fun s => StackWritable s 0 8 ∧ Buffer s z 32 false ∧ Buffer s x 32 false)
      (fun s s' => (s'.regs 0) = BitVec.ofInt 64 (Spec.cmp (valueAt s z 32) (valueAt s x 32))) := by
  intro ret hret s hs ⟨⟨_, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩⟩
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  simp only [valueAt]
  janus64_run [Util.readLE_32]
  all_goals ((try have := Util.readLE8_lt s.mem (z.toNat )); (try have := Util.readLE8_lt s.mem (z.toNat + 8)); (try have := Util.readLE8_lt s.mem (z.toNat + 16)); (try have := Util.readLE8_lt s.mem (z.toNat + 24)); (try have := Util.readLE8_lt s.mem (x.toNat )); (try have := Util.readLE8_lt s.mem (x.toNat + 8)); (try have := Util.readLE8_lt s.mem (x.toNat + 16)); (try have := Util.readLE8_lt s.mem (x.toNat + 24)); have hl := Util.lt_out_iff _ _ _ _ _ _ _ _ (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24)); simp only [Util.cmp_ofInt]; (simp only [Util.subFlags_fst_toNat, BitVec.toNat_or, BitVec.toNat_sub, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.or_eq_zero_iff, Nat.reducePow, Nat.reduceMod, Util.ite_one_toNat] at *); dec_facts; (repeat' split) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Bool.false_eq_true, Bool.true_eq_false, BitVec.reduceEq]) <;> first | rfl | omega)

namespace Wit

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
    (StackWritable s 0 8 ∧ Buffer s z 32 false ∧ Buffer s x 32 false) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ (s'.regs 0) = BitVec.ofInt 64 (Spec.cmp (valueAt s z 32) (valueAt s x 32)) :=
  ⟨ret, s0, z, x, hret, setup, hpre,
    correctness_proof z x ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0) = 0#64 := by
  refine (correctness_proof z x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [valueAt]
  decide

end Wit

end Fv256.Amd64.Cmp
