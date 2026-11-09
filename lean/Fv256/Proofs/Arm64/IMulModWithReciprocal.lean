import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Arm64.ReduceSpec
import Fv256.Proofs.Arm64.IMulModWithReciprocalCore
import Fv256.Proofs.Arm64.R4Sum

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

set_option exponentiation.threshold 600

namespace Fv256.Arm64.IMulModWithReciprocal

theorem correctness_proof (z x m mu : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, m, mu]
      (fun s => GuardOK s 784 ∧ s.sp.toNat % 16 = 0 ∧ 824 ≤ s.sp.toNat ∧ s.sp.toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (s.sp.toNat - 824) 824 true = true ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 824) 824 ∧
        Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem m false ∧ (mu.toNat + 40 ≤ 2 ^ 48 ∧ s.mem.accessible mu.toNat 40 false = true) ∧
        Apart z.toNat 32 (s.sp.toNat - 824) 824 ∧ Apart x.toNat 32 (s.sp.toNat - 824) 824 ∧
        Apart m.toNat 32 (s.sp.toNat - 824) 824 ∧ Apart mu.toNat 40 (s.sp.toNat - 824) 824 ∧
        Fv256.F.MuOK (val256 s.mem m.toNat) (s.mem.readLE mu.toNat 40))
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Fv256.F.mulmodSpec (val256 s.mem z.toNat) (val256 s.mem x.toNat) (val256 s.mem m.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 824, s.sp.toNat - 8)])  :=
  Fv256.Arm64.IMulModRecCore.correctness_param Fv256.Arm64.R4Seg.r4_summary z x m mu

namespace Wit

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

set_option maxRecDepth 200000 in
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 0x20)
def m : BitVec 64 := BitVec.ofNat 64 (DST + 0x40)
def mu : BitVec 64 := BitVec.ofNat 64 (DST + 0x60)

/-- witness memory: `z = 3`, `x = 5`, `m = 2^248`, `mu = 2^264 - 1 = ⌊(2^512-1)/m⌋` (four limbs: the reduce4 path runs) on top of the standard witness memory -/
def wm : Memory :=
  { Janus.Contracts.EqHashModel.wmem with
    bytes := fun a => if a = DST then 3 else if a = DST + 0x20 then 5 else if a = DST + 0x40 + 31 then 1
      else if DST + 0x60 ≤ a ∧ a < DST + 0x60 + 33 then 255 else Janus.Contracts.EqHashModel.wmem.bytes a }

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then x else if i = 2 then m else if i = 3 then mu
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wm }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, m, mu] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : GuardOK s0 784 ∧ s0.sp.toNat % 16 = 0 ∧ 824 ≤ s0.sp.toNat ∧ s0.sp.toNat ≤ 2 ^ 48 ∧
        s0.mem.accessible (s0.sp.toNat - 824) 824 true = true ∧
        Apart ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 824) 824 ∧
        Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧ Ptr32 s0.mem m false ∧ (mu.toNat + 40 ≤ 2 ^ 48 ∧ s0.mem.accessible mu.toNat 40 false = true) ∧
        Apart z.toNat 32 (s0.sp.toNat - 824) 824 ∧ Apart x.toNat 32 (s0.sp.toNat - 824) 824 ∧
        Apart m.toNat 32 (s0.sp.toNat - 824) 824 ∧ Apart mu.toNat 40 (s0.sp.toNat - 824) 824 ∧
        Fv256.F.MuOK (val256 s0.mem m.toNat) (s0.mem.readLE mu.toNat 40) := by
  refine ⟨by unfold GuardOK; decide, by decide, by decide, by decide, by decide, ?_,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (first | (unfold Apart; decide) | skip)
  show Fv256.F.MuOK (s0.mem.readLE m.toNat 32) (s0.mem.readLE mu.toNat 40)
  have hm : s0.mem.readLE m.toNat 32 = 2 ^ 248 := by decide
  have hu : s0.mem.readLE mu.toNat 40 = 2 ^ 264 - 1 := by decide
  rw [hm, hu]
  intro _
  unfold Fv256.F.RecipWeak Fv256.F.recipExact
  constructor <;> decide

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x m mu : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, m, mu] s ∧
    (GuardOK s 784 ∧ s.sp.toNat % 16 = 0 ∧ 824 ≤ s.sp.toNat ∧ s.sp.toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (s.sp.toNat - 824) 824 true = true ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 824) 824 ∧
        Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem m false ∧ (mu.toNat + 40 ≤ 2 ^ 48 ∧ s.mem.accessible mu.toNat 40 false = true) ∧
        Apart z.toNat 32 (s.sp.toNat - 824) 824 ∧ Apart x.toNat 32 (s.sp.toNat - 824) 824 ∧
        Apart m.toNat 32 (s.sp.toNat - 824) 824 ∧ Apart mu.toNat 40 (s.sp.toNat - 824) 824 ∧
        Fv256.F.MuOK (val256 s.mem m.toNat) (s.mem.readLE mu.toNat 40)) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Fv256.F.mulmodSpec (val256 s.mem z.toNat) (val256 s.mem x.toNat) (val256 s.mem m.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 824, s.sp.toNat - 8)] :=
  ⟨ret, s0, z, x, m, mu, hret, setup, hpre,
    correctness_proof z x m mu ret hret s0 setup hpre⟩

end Wit

end Fv256.Arm64.IMulModWithReciprocal
