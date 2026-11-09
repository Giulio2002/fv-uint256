import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).GtUint64(n uint64) bool` (arm64)

**Guarantee.** For every pointer `z` (the receiver, `X0`) and every `n` (`X1`) such that the 32 bytes at `z` are readable (below `2^48`), the call returns (no fault, no panic), obeys the ABI, and the `bool` result is `Fv256.Spec.gt` of the number at the receiver and `n` (`X0`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns the value for `z = 0`, `n = 0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.GtUint64


theorem correctness (z n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, n]
      (fun s => Ptr32 s.mem z false)
      (fun s s' => (s'.regs 0).toNat % 256 = (Spec.gt (val256 s.mem z.toNat) n.toNat).toNat) := by
  intro ret hret s hs ⟨hz, hz'⟩
  janus_intro hs
  janus_run
  all_goals ((try have := Util.readLE8_lt s.mem (z.toNat)); (try have := Util.readLE8_lt s.mem (z.toNat + 8)); (try have := Util.readLE8_lt s.mem (z.toNat + 16)); (try have := Util.readLE8_lt s.mem (z.toNat + 24)); (try simp only [janus_post] at *); (try simp only [Nat.or_eq_zero_iff] at *); simp only [Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod] at *; simp only [Spec.gt]; dec_facts; (repeat' split) <;> (try simp only [BitVec.reduceEq, BitVec.reduceNe, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]) <;> first | omega | rfl)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def n : BitVec 64 := 0#64

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then n else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hpre : Ptr32 s0.mem z false := ⟨by decide, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s ∧
    (Ptr32 s.mem z false) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ (s'.regs 0).toNat % 256 = (Spec.gt (val256 s.mem z.toNat) n.toNat).toNat :=
  ⟨ret, s0, z, n, hret, setup, hpre,
    correctness z n ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat % 256 = 0 := by
  refine (correctness z n ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  try simp only [val256]
  decide

end Witness

end Fv256.Arm64.GtUint64
