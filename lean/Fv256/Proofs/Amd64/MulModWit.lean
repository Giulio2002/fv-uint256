import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Amd64.MulModSum

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MulMod.Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

set_option maxRecDepth 100000 in
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 0x20)
def y : BitVec 64 := BitVec.ofNat 64 (DST + 0x40)
def m : BitVec 64 := BitVec.ofNat 64 (DST + 0x60)

/-- witness memory: `x = 3`, `y = 5`, `m = 2^248 + 7` (four limbs: the reciprocal path runs) on top of the standard amd64 witness memory -/
def wm : Memory :=
  { wmem64 with
    bytes := fun a => if a = DST + 0x20 then 3 else if a = DST + 0x40 then 5 else if a = DST + 0x60 then 7
      else if a = DST + 0x60 + 31 then 1 else wmem64.bytes a }

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then x else if i = 1 then y else if i = 7 then m
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wm }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y, m] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem hpre : (StackGuardOK s0 0x2f0 ∧ 0x380 ≤ (s0.regs regSP).toNat ∧ StackWritable s0 0x378 0x28 ∧
        Buffer s0 z 32 true ∧ Buffer s0 x 32 false ∧ Buffer s0 y 32 false ∧ Buffer s0 m 32 false ∧
        Apart z.toNat 32 (((s0.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart x.toNat 32 (((s0.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart y.toNat 32 (((s0.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart m.toNat 32 (((s0.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart ((s0.regs regG).toNat + 16) 8 (((s0.regs regSP).toNat) - 0x378) 0x3a0) := by
  refine ⟨⟨by decide, by decide, by decide⟩, by unfold regSP; decide, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try unfold Apart); (try unfold regSP); (try unfold regG); decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y, m] s ∧
    (StackGuardOK s 0x2f0 ∧ 0x380 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x378 0x28 ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s m 32 false ∧
        Apart z.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart x.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart y.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart m.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart ((s.regs regG).toNat + 16) 8 (((s.regs regSP).toNat) - 0x378) 0x3a0) :=
  ⟨ret, s0, z, x, y, m, hret, setup, hpre⟩

end Fv256.Amd64.MulMod.Witness
