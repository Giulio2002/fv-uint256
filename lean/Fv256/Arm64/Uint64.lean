import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).Uint64()` (arm64)

**Guarantee.** For every pointer `x` (the receiver, `X0`) and every Go call state such that the 32 bytes at `x` are readable
(below `2^48`), the call returns (no fault, no panic), obeys the ABI, and the result (`X0`/`RAX`) is the low 64 bits of the 256-bit little-endian number at `x` (`Fv256.Spec.uint64`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: the result for the zero number.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Uint64

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x] (fun s => Ptr32 s.mem x false)
      (fun s s' => (s'.regs 0).toNat = Spec.uint64 (val256 s.mem x.toNat)) := by
  intro ret hret s hs ⟨hx, hx'⟩
  janus_intro hs
  janus_run
  all_goals ((try have := Util.readLE8_lt s.mem (x.toNat )); (try have := Util.readLE8_lt s.mem (x.toNat + 8)); (try have := Util.readLE8_lt s.mem (x.toNat + 16)); (try have := Util.readLE8_lt s.mem (x.toNat + 24)); simp only [Spec.uint64, Nat.reducePow]; omega)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def x : BitVec 64 := BitVec.ofNat 64 DST

def s0 : State :=
  { regs := fun i => if i = 0 then x else if i = 28 then BitVec.ofNat 64 wg
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩

theorem hpre : Ptr32 s0.mem x false := ⟨by decide, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧ Ptr32 s.mem x false :=
  ⟨ret, s0, x, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = 0 := by
  refine (correctness x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  decide

end Witness

end Fv256.Arm64.Uint64
