import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Arm64.MulModDefs
import Fv256.Proofs.Arm64.ReduceSpec
import Fv256.Proofs.Arm64.MulModSum
import Fv256.Proofs.Arm64.MulModCorr

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.MulModCorr.Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

set_option maxRecDepth 200000 in
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 0x20)
def y : BitVec 64 := BitVec.ofNat 64 (DST + 0x40)
def m : BitVec 64 := BitVec.ofNat 64 (DST + 0x60)

/-- witness memory: `x = 3`, `y = 5`, `m = 2^248 + 7` (four limbs: the reciprocal path runs) on top of the standard witness memory -/
def wm : Memory :=
  { Janus.Contracts.EqHashModel.wmem with
    bytes := fun a => if a = DST + 0x20 then 3 else if a = DST + 0x40 then 5 else if a = DST + 0x60 then 7
      else if a = DST + 0x60 + 31 then 1 else Janus.Contracts.EqHashModel.wmem.bytes a }

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then x else if i = 2 then y else if i = 3 then m
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wm }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y, m] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : GuardOK s0 768 ∧ s0.sp.toNat % 16 = 0 ∧ 808 ≤ s0.sp.toNat ∧ s0.sp.toNat + 40 ≤ 2 ^ 48 ∧
        s0.mem.accessible (s0.sp.toNat - 808) (808 + 40) true = true ∧
        Apart ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 808) 848 ∧
        Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧ Ptr32 s0.mem y false ∧ Ptr32 s0.mem m false ∧
        Apart z.toNat 32 (s0.sp.toNat - 808) 848 ∧ Apart x.toNat 32 (s0.sp.toNat - 808) 848 ∧
        Apart y.toNat 32 (s0.sp.toNat - 808) 848 ∧ Apart m.toNat 32 (s0.sp.toNat - 808) 848 := by
  refine ⟨by unfold GuardOK; decide, by decide, by decide, by decide, by decide, ?_,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_, ?_⟩ <;>
    (unfold Apart; decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y, m] s ∧
    (GuardOK s 768 ∧ s.sp.toNat % 16 = 0 ∧ 808 ≤ s.sp.toNat ∧ s.sp.toNat + 40 ≤ 2 ^ 48 ∧
        s.mem.accessible (s.sp.toNat - 808) (808 + 40) true = true ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 808) 848 ∧
        Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Ptr32 s.mem m false ∧
        Apart z.toNat 32 (s.sp.toNat - 808) 848 ∧ Apart x.toNat 32 (s.sp.toNat - 808) 848 ∧
        Apart y.toNat 32 (s.sp.toNat - 808) 848 ∧ Apart m.toNat 32 (s.sp.toNat - 808) 848) :=
  ⟨ret, s0, z, x, y, m, hret, setup, hpre⟩

end Fv256.Arm64.MulModCorr.Witness
