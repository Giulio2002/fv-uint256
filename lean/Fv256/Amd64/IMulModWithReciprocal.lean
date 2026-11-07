import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecF
import Fv256.Amd64.IMulModWithReciprocalCore
import Fv256.Amd64.ReduceSpec
import Fv256.Amd64.Reduce4

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

set_option exponentiation.threshold 600

namespace Fv256.Amd64.IMulModWithReciprocal

abbrev Pre := Fv256.Amd64.IMulModWithReciprocalCore.Pre

theorem correctness (z x m : BitVec 64) (mu : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, m, mu] (Pre z x m mu)
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Fv256.F.mulmodSpec (valueAt s z 32) (valueAt s x 32) (valueAt s m 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x320, (s.regs regSP).toNat)])  :=
  Fv256.Amd64.IMulModWithReciprocalCore.correctness_param Fv256.Amd64.Reduce4.reduce4_summary z x m mu

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

set_option maxRecDepth 100000 in
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 0x20)
def m : BitVec 64 := BitVec.ofNat 64 (DST + 0x40)
def mu : BitVec 64 := BitVec.ofNat 64 (DST + 0x60)

/-- witness memory: `z = 3`, `x = 5`, `m = 2^248`, `mu = 2^264 - 1` (four limbs: the reduce4 path runs) on top of the standard amd64 witness memory -/
def wm : Memory :=
  { wmem64 with
    bytes := fun a => if a = DST then 3 else if a = DST + 0x20 then 5 else if a = DST + 0x40 + 31 then 1
      else if DST + 0x60 ≤ a ∧ a < DST + 0x60 + 33 then 255 else wmem64.bytes a }

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then x else if i = 1 then m else if i = 7 then mu
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wm }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, m, mu] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : Pre z x m mu s0 := by
  unfold Pre Fv256.Amd64.IMulModWithReciprocalCore.Pre
  refine ⟨⟨by decide, by decide, by decide⟩, by unfold regSP; decide, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (first | ((try unfold Apart); (try unfold regSP); (try unfold regG); decide) | skip)
  show Fv256.F.MuOK (valueAt s0 m 32) (s0.mem.readLE mu.toNat 40)
  simp only [valueAt]
  have hm : s0.mem.readLE m.toNat 32 = 2 ^ 248 := by decide
  have hu : s0.mem.readLE mu.toNat 40 = 2 ^ 264 - 1 := by decide
  rw [hm, hu]
  intro _
  unfold Fv256.F.RecipWeak Fv256.F.recipExact
  constructor <;> decide

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x m mu : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, m, mu] s ∧ Pre z x m mu s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        valueAt s' z 32 = Fv256.F.mulmodSpec (valueAt s z 32) (valueAt s x 32) (valueAt s m 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x320, (s.regs regSP).toNat)] :=
  ⟨ret, s0, z, x, m, mu, hret, setup, hpre,
    correctness z x m mu ret hret s0 setup hpre⟩

end Witness


end Fv256.Amd64.IMulModWithReciprocal
