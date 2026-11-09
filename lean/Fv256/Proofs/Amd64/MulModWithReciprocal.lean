import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Amd64.MulModRecCorr
import Fv256.Proofs.Amd64.ReduceSpec
import Fv256.Proofs.Amd64.Reduce4

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MulModWithReciprocal

theorem correctness_proof (z x y m mu : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, m, mu]
      (fun s => StackGuardOK s 0x298 ∧ 0x2f0 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x2e8 0x30 ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s m 32 false ∧ Buffer s mu 40 false ∧
        Apart z.toNat 32 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Apart x.toNat 32 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Apart y.toNat 32 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Apart m.toNat 32 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Apart mu.toNat 40 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Fv256.F.MuOK (valueAt s m 32) (s.mem.readLE mu.toNat 40) ∧
        Apart ((s.regs regG).toNat + 16) 8 (((s.regs regSP).toNat) - 0x2e8) 0x318)
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Fv256.F.mulmodSpec (valueAt s x 32) (valueAt s y 32) (valueAt s m 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x2e8, (s.regs regSP).toNat),
          ((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 0x30)])  :=
  Fv256.Amd64.MulModRecCorr.correctness_param Fv256.Amd64.Reduce4.reduce4_summary z x y m mu

set_option exponentiation.threshold 600
namespace Wit

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

set_option maxRecDepth 100000 in
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 0x20)
def y : BitVec 64 := BitVec.ofNat 64 (DST + 0x40)
def m : BitVec 64 := BitVec.ofNat 64 (DST + 0x60)
def mu : BitVec 64 := BitVec.ofNat 64 (DST + 0x80)

/-- witness memory: `x = 3`, `y = 5`, `m = 2^248`, `mu = 2^264 - 1 = ⌊(2^512-1)/m⌋` (four limbs: the reduce4 path runs) on top of the standard amd64 witness memory -/
def wm : Memory :=
  { wmem64 with
    bytes := fun a => if a = DST + 0x20 then 3 else if a = DST + 0x40 then 5 else if a = DST + 0x60 + 31 then 1
      else if DST + 0x80 ≤ a ∧ a < DST + 0x80 + 33 then 255 else wmem64.bytes a }

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then x else if i = 1 then y else if i = 7 then m else if i = 6 then mu
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wm }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y, m, mu] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem hpre : (StackGuardOK s0 0x298 ∧ 0x2f0 ≤ (s0.regs regSP).toNat ∧ StackWritable s0 0x2e8 0x30 ∧
        Buffer s0 z 32 true ∧ Buffer s0 x 32 false ∧ Buffer s0 y 32 false ∧ Buffer s0 m 32 false ∧ Buffer s0 mu 40 false ∧
        Apart z.toNat 32 (((s0.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Apart x.toNat 32 (((s0.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Apart y.toNat 32 (((s0.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Apart m.toNat 32 (((s0.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Apart mu.toNat 40 (((s0.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Fv256.F.MuOK (valueAt s0 m 32) (s0.mem.readLE mu.toNat 40) ∧
        Apart ((s0.regs regG).toNat + 16) 8 (((s0.regs regSP).toNat) - 0x2e8) 0x318) := by
  refine ⟨⟨by decide, by decide, by decide⟩, by unfold regSP; decide, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (first | ((try unfold Apart); (try unfold regSP); (try unfold regG); decide) | skip)
  show Fv256.F.MuOK (s0.mem.readLE m.toNat 32) (s0.mem.readLE mu.toNat 40)
  have hm : s0.mem.readLE m.toNat 32 = 2 ^ 248 := by decide
  have hu : s0.mem.readLE mu.toNat 40 = 2 ^ 264 - 1 := by decide
  rw [hm, hu]
  intro _
  unfold Fv256.F.RecipWeak Fv256.F.recipExact
  constructor <;> decide

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y m mu : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y, m, mu] s ∧
    (StackGuardOK s 0x298 ∧ 0x2f0 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x2e8 0x30 ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s m 32 false ∧ Buffer s mu 40 false ∧
        Apart z.toNat 32 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Apart x.toNat 32 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Apart y.toNat 32 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Apart m.toNat 32 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Apart mu.toNat 40 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Fv256.F.MuOK (valueAt s m 32) (s.mem.readLE mu.toNat 40) ∧
        Apart ((s.regs regG).toNat + 16) 8 (((s.regs regSP).toNat) - 0x2e8) 0x318) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        valueAt s' z 32 = Fv256.F.mulmodSpec (valueAt s x 32) (valueAt s y 32) (valueAt s m 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x2e8, (s.regs regSP).toNat),
          ((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 0x30)] :=
  ⟨ret, s0, z, x, y, m, mu, hret, setup, hpre,
    correctness_proof z x y m mu ret hret s0 setup hpre⟩

end Wit

end Fv256.Amd64.MulModWithReciprocal
