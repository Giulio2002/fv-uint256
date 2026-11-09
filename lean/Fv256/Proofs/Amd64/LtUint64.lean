import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).LtUint64(n uint64) bool` (amd64)

**Guarantee.** For every pointer `z` (the receiver, `RAX`) and every `n` (`RBX`) such that the return-address slot is writable and the 32 bytes at `z` are readable (below `2^48`), the call returns (no fault, no panic), obeys the ABI, and the `bool` result is `Fv256.Spec.lt` of the number at the receiver and `n` (`RAX`).

**Non-vacuity.** `Wit.nonvacuous`: a concrete call satisfies the precondition; `Wit.returns`: it returns the value for `z = 0`, `n = 0`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.LtUint64

set_option maxHeartbeats 8000000 in
theorem correctness_proof (z n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, n]
      (fun s => StackWritable s 0 8 ∧ Buffer s z 32 false)
      (fun s s' => (s'.regs 0).toNat % 256 = (Spec.lt (valueAt s z 32) n.toNat).toNat) := by
  intro ret hret s hs ⟨⟨_, hnw, hacc⟩, ⟨hzw, hz⟩⟩
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  simp only [valueAt]
  janus64_run [Util.readLE_32]
  all_goals ((try have := Util.readLE8_lt s.mem (z.toNat)); (try have := Util.readLE8_lt s.mem (z.toNat + 8)); (try have := Util.readLE8_lt s.mem (z.toNat + 16)); (try have := Util.readLE8_lt s.mem (z.toNat + 24)); (try simp only [Nat.or_eq_zero_iff, BitVec.toNat_or, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod] at *); simp only [Spec.lt]; (try simp only [BitVec.toNat_setWidth, Nat.zero_or, Bool.false_eq_true, Bool.true_eq_false, Nat.reduceOr, not_true_eq_false] at *); dec_facts; (repeat' split) <;> (try simp only [BitVec.reduceEq, BitVec.reduceNe, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Bool.false_eq_true, Bool.true_eq_false, Nat.reduceOr, not_true_eq_false] at *) <;> first | rfl | omega)

namespace Wit

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def n : BitVec 64 := 0#64

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then n else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackWritable s0 0 8 ∧ Buffer s0 z 32 false :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s ∧
    (StackWritable s 0 8 ∧ Buffer s z 32 false) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ (s'.regs 0).toNat % 256 = (Spec.lt (valueAt s z 32) n.toNat).toNat :=
  ⟨ret, s0, z, n, hret, setup, hpre,
    correctness_proof z n ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat % 256 = 0 := by
  refine (correctness z n ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [valueAt]
  decide

end Wit

end Fv256.Amd64.LtUint64
