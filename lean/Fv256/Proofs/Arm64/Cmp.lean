import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).Cmp(x *Int) int` (arm64)

**Guarantee.** For all pointers `z` (receiver, `X0`) and `x` (`X1`) such that the 32 bytes at each are readable
(below `2^48`; they may be equal or overlap arbitrarily) the call returns (no fault, no panic), obeys the ABI, and
the `int` result is `Fv256.Spec.cmp` of the number at the receiver and the number at `x` (`X0`, read as a signed 64-bit integer: -1, 0 or 1), the numbers being read before the call.

**Non-vacuity.** `Wit.nonvacuous`: a concrete call satisfies the precondition; `Wit.returns`: it returns `0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Cmp

theorem correctness_proof (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x]
      (fun s => Ptr32 s.mem z false ∧ Ptr32 s.mem x false)
      (fun s s' => (s'.regs 0) = BitVec.ofInt 64 (Spec.cmp (val256 s.mem z.toNat) (val256 s.mem x.toNat))) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hx, hx'⟩⟩
  janus_intro hs
  janus_run
  all_goals ((try have := Util.readLE8_lt s.mem (z.toNat)); (try have := Util.readLE8_lt s.mem (z.toNat + 8)); (try have := Util.readLE8_lt s.mem (z.toNat + 16)); (try have := Util.readLE8_lt s.mem (z.toNat + 24)); (try have := Util.readLE8_lt s.mem (x.toNat)); (try have := Util.readLE8_lt s.mem (x.toNat + 8)); (try have := Util.readLE8_lt s.mem (x.toNat + 16)); (try have := Util.readLE8_lt s.mem (x.toNat + 24)); (try simp only [janus_post] at *); (try simp only [Nat.or_eq_zero_iff] at *); simp only [Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod] at *; have hb := Util.borrow4_dec _ _ _ _ _ _ _ _ (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24)); have hzz := Util.zero4_iff _ _ _ _ _ _ _ _ (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24)); (try simp only [hb, hzz, Util.ite01_eq1, Util.ite01_eq0] at *); simp only [Util.cmp_ofInt]; dec_facts; (repeat' split) <;> (try simp only [BitVec.reduceEq, BitVec.reduceNe]) <;> first | rfl | omega)

namespace Wit

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then x
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hpre : Ptr32 s0.mem z false ∧ Ptr32 s0.mem x false :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧
    (Ptr32 s.mem z false ∧ Ptr32 s.mem x false) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ (s'.regs 0) = BitVec.ofInt 64 (Spec.cmp (val256 s.mem z.toNat) (val256 s.mem x.toNat)) :=
  ⟨ret, s0, z, x, hret, setup, hpre,
    correctness_proof z x ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0) = 0#64 := by
  refine (correctness z x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  decide

end Wit

end Fv256.Arm64.Cmp
