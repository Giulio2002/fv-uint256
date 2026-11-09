import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Arm64.ReduceSpec
import Fv256.Proofs.Arm64.IMulModCore
import Fv256.Proofs.Arm64.R4Sum
import Fv256.Proofs.Arm64.RecipSummary
import Fv256.Proofs.Arm64.MulModDefs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

set_option exponentiation.threshold 600

namespace Fv256.Arm64.IMulMod

theorem correctness (z x m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, m]
      (fun s => GuardOK s 816 ∧ s.sp.toNat % 16 = 0 ∧ 856 ≤ s.sp.toNat ∧ s.sp.toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (s.sp.toNat - 856) 856 true = true ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 856) 856 ∧
        Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem m false ∧
        Apart z.toNat 32 (s.sp.toNat - 856) 856 ∧ Apart x.toNat 32 (s.sp.toNat - 856) 856 ∧
        Apart m.toNat 32 (s.sp.toNat - 856) 856)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Fv256.F.mulmodSpec (val256 s.mem z.toNat) (val256 s.mem x.toNat) (val256 s.mem m.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 856, s.sp.toNat - 8)])  :=
  Fv256.Arm64.IMulModCore.correctness_param (Fv256.Arm64.MulModDefs.recipU_of Fv256.Arm64.RecipSeg.recip_summary)
    Fv256.Arm64.R4Seg.r4_summary z x m

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

set_option maxRecDepth 200000 in
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 0x20)
def m : BitVec 64 := BitVec.ofNat 64 (DST + 0x40)

/-- witness memory: `z = 3`, `x = 5`, `m = 2^248 + 7`, (four limbs: the reduce4 path runs) on top of the standard witness memory -/
def wm : Memory :=
  { Janus.Contracts.EqHashModel.wmem with
    bytes := fun a => if a = DST then 3 else if a = DST + 0x20 then 5 else if a = DST + 0x40 + 31 then 1
      else if a = DST + 0x40 then 7 else Janus.Contracts.EqHashModel.wmem.bytes a }

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then x else if i = 2 then m
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wm }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, m] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : GuardOK s0 816 ∧ s0.sp.toNat % 16 = 0 ∧ 856 ≤ s0.sp.toNat ∧ s0.sp.toNat ≤ 2 ^ 48 ∧
        s0.mem.accessible (s0.sp.toNat - 856) 856 true = true ∧
        Apart ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 856) 856 ∧
        Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧ Ptr32 s0.mem m false ∧
        Apart z.toNat 32 (s0.sp.toNat - 856) 856 ∧ Apart x.toNat 32 (s0.sp.toNat - 856) 856 ∧
        Apart m.toNat 32 (s0.sp.toNat - 856) 856 := by
  refine ⟨by unfold GuardOK; decide, by decide, by decide, by decide, by decide, ?_,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_⟩ <;>
    (first | (unfold Apart; decide) | skip)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, m] s ∧
    (GuardOK s 816 ∧ s.sp.toNat % 16 = 0 ∧ 856 ≤ s.sp.toNat ∧ s.sp.toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (s.sp.toNat - 856) 856 true = true ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 856) 856 ∧
        Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem m false ∧
        Apart z.toNat 32 (s.sp.toNat - 856) 856 ∧ Apart x.toNat 32 (s.sp.toNat - 856) 856 ∧
        Apart m.toNat 32 (s.sp.toNat - 856) 856 ) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Fv256.F.mulmodSpec (val256 s.mem z.toNat) (val256 s.mem x.toNat) (val256 s.mem m.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 856, s.sp.toNat - 8)] :=
  ⟨ret, s0, z, x, m, hret, setup, hpre,
    correctness z x m ret hret s0 setup hpre⟩

end Witness

end Fv256.Arm64.IMulMod
