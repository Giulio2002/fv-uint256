import sys
isa,fn,op,wval=sys.argv[1],sys.argv[2],sys.argv[3],sys.argv[4]
tail=sys.argv[5] if len(sys.argv)>5 else 'done'
doc=sys.argv[6] if len(sys.argv)>6 else f'the `bool` result is `Fv256.Spec.{op}` of the number at the receiver and the number at `x`'
if isa=='arm64':
    print(f'''import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).{fn}(x *Int) bool` (arm64)

**Guarantee.** For all pointers `z` (receiver, `X0`) and `x` (`X1`) such that the 32 bytes at each are readable
(below `2^48`; they may be equal or overlap arbitrarily) the call returns (no fault, no panic), obeys the ABI, and
{doc} (low byte of `X0`), the numbers being read before the call.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `{wval}`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.{fn}

theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x]
      (fun s => Ptr32 s.mem z false ∧ Ptr32 s.mem x false)
      (fun s s' => (s'.regs 0).toNat % 256 = (Spec.{op} (val256 s.mem z.toNat) (val256 s.mem x.toNat)).toNat) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hx, hx'⟩⟩
  janus_intro hs
  janus_run
  all_goals ({tail})

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  {{ regs := fun i => if i = 0 then z else if i = 1 then x
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }}

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hpre : Ptr32 s0.mem z false ∧ Ptr32 s0.mem x false :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧
    (Ptr32 s.mem z false ∧ Ptr32 s.mem x false) :=
  ⟨ret, s0, z, x, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat % 256 = {wval} := by
  refine (correctness z x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  decide

end Witness

end Fv256.Arm64.{fn}''')
else:
    print(f'''import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).{fn}(x *Int) bool` (amd64)

**Guarantee.** For all pointers `z` (receiver, `RAX`) and `x` (`RBX`) such that the return-address slot is writable and
the 32 bytes at each are readable (below `2^48`; they may be equal or overlap arbitrarily) the call returns (no fault,
no panic), obeys the ABI, and {doc} (`AL`, low byte of `RAX`), the numbers being read before the call.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `{wval}`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.{fn}

theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x]
      (fun s => StackWritable s 0 8 ∧ Buffer s z 32 false ∧ Buffer s x 32 false)
      (fun s s' => (s'.regs 0).toNat % 256 = (Spec.{op} (valueAt s z 32) (valueAt s x 32)).toNat) := by
  intro ret hret s hs ⟨⟨_, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩⟩
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  simp only [valueAt]
  janus64_run [Util.readLE_32]
  all_goals ({tail})

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  {{ regs := fun i => if i = 0 then z else if i = 3 then x else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }}

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
    ABIReturn s0 s' ∧ (s'.regs 0).toNat % 256 = {wval} := by
  refine (correctness z x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [valueAt]
  decide

end Witness

end Fv256.Amd64.{fn}''')
