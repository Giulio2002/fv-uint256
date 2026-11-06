import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecF
import Fv256.Arm64.SummaryEnsures
import Fv256.Arm64.AddMod

/-!
# `(*uint256.Int).AddMod(x, y, m *Int) *Int` (arm64): correctness and non-vacuity

`correctness` is `Fv256.Arm64.AddMod.addmod_summary` transferred to an `Ensures` statement over `Fv256.F.addmodSpec`
(see `Fv256.Arm64.AddMod` for the guarantee). `Witness.nonvacuous` exhibits a concrete call (the read-only data of the
binary loaded) satisfying the whole precondition.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.AddModMain

theorem correctness (z x y m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, m]
      (fun s => GuardOK s 816 ∧ s.sp.toNat % 16 = 0 ∧ 856 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 48 ∧
        s.mem.accessible (s.sp.toNat - 856) 872 true = true ∧ Extracted.program.DataLoaded s.mem ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 856 ∨ s.sp.toNat + 16 ≤ (s.regs 28).toNat + 16) ∧
        Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Ptr32 s.mem m false ∧
        Disjoint z.toNat 32 (s.sp.toNat - 856) 872 ∧ Disjoint x.toNat 32 (s.sp.toNat - 856) 872 ∧
        Disjoint y.toNat 32 (s.sp.toNat - 856) 872 ∧ Disjoint m.toNat 32 (s.sp.toNat - 856) 872 ∧
        (z = m ∨ z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat) ∧
        (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
        (z = y ∨ z.toNat + 32 ≤ y.toNat ∨ y.toNat + 32 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 24 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 28).toNat + 16))
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Fv256.F.addmodSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) (val256 s.mem m.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 856, s.sp.toNat + 16)]) := by
  refine Fv256.Arm64.SummaryEnsures.ensures_of_summary _ _ Fv256.Arm64.AddMod.addmod_summary ?_ ?_
  · intro ret hret s hsu ⟨hg, hsal, hsb, hsc, hsw, hdata, hgw, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, ⟨hm, hm'⟩, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩
    have h30 : s.regs 30 = BitVec.ofNat 64 ret := by
      have := hsu.lr; exact this
    have h0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have h1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    have h2 : s.regs 2 = y := by have := hsu.args 2 (by simp); simpa using this
    have h3 : s.regs 3 = m := by have := hsu.args 3 (by simp); simpa using this
    rw [h30, h0, h1, h2, h3]
    have ha := hret.aligned
    have hu := hret.user
    refine ⟨?_, ?_, hg, hsal, hsb, hsc, hsw, hdata, hgw, hz', hz, hx', hx, hy', hy, hm', hm, ?_, ?_, ?_, ?_, hzm, hzx, hzy, hgz⟩
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [Disjoint] at hdz; omega
    · simp only [Disjoint] at hdx; omega
    · simp only [Disjoint] at hdy; omega
    · simp only [Disjoint] at hdm; omega
  · intro ret hret s hsu ⟨hg, hsal, hsb, hsc, hsw, hdata, hgw, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, ⟨hm, hm'⟩, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩ s' ⟨hpc, hsp, h0, h18, h28, h29, h30, hv, hf⟩
    have e0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have e1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    have e2 : s.regs 2 = y := by have := hsu.args 2 (by simp); simpa using this
    have e3 : s.regs 3 = m := by have := hsu.args 3 (by simp); simpa using this
    rw [e0, e1, e2, e3] at hv
    rw [e0] at hf h0
    refine ⟨⟨hsp, h28, h29, h18⟩, ?_, ?_, hf⟩
    · exact h0
    · exact hv

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

set_option maxRecDepth 200000 in
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def zp : Nat := 0x30800

def dsegs : List DataSegment := Extracted.program.data

/-- the read-only data of the binary, zero elsewhere -/
def bytes (a : Nat) : Byte :=
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def z : BitVec 64 := BitVec.ofNat 64 zp
def x : BitVec 64 := BitVec.ofNat 64 (zp + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then x else if i = 2 then x else if i = 3 then x
      else if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 856, 872, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, true⟩] ++ dregs⟩ }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, x, x] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hpre : GuardOK s0 816 ∧ s0.sp.toNat % 16 = 0 ∧ 856 ≤ s0.sp.toNat ∧ s0.sp.toNat + 16 ≤ 2 ^ 48 ∧
    s0.mem.accessible (s0.sp.toNat - 856) 872 true = true ∧ Extracted.program.DataLoaded s0.mem ∧
    ((s0.regs 28).toNat + 24 ≤ s0.sp.toNat - 856 ∨ s0.sp.toNat + 16 ≤ (s0.regs 28).toNat + 16) ∧
    Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧ Ptr32 s0.mem x false ∧ Ptr32 s0.mem x false ∧
    Disjoint z.toNat 32 (s0.sp.toNat - 856) 872 ∧ Disjoint x.toNat 32 (s0.sp.toNat - 856) 872 ∧
    Disjoint x.toNat 32 (s0.sp.toNat - 856) 872 ∧ Disjoint x.toNat 32 (s0.sp.toNat - 856) 872 ∧
    (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
    (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
    (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
    ((s0.regs 28).toNat + 24 ≤ z.toNat ∨ z.toNat + 32 ≤ (s0.regs 28).toNat + 16) := by
  refine ⟨by unfold GuardOK; decide, by decide, by decide, by decide, by decide, dataLoaded, by decide,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_, ?_,
    by decide, by decide, by decide, by decide⟩ <;>
    (unfold Disjoint; decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y, m] s ∧
    (GuardOK s 816 ∧ s.sp.toNat % 16 = 0 ∧ 856 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 48 ∧
      s.mem.accessible (s.sp.toNat - 856) 872 true = true ∧ Extracted.program.DataLoaded s.mem ∧
      ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 856 ∨ s.sp.toNat + 16 ≤ (s.regs 28).toNat + 16) ∧
      Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Ptr32 s.mem m false ∧
      Disjoint z.toNat 32 (s.sp.toNat - 856) 872 ∧ Disjoint x.toNat 32 (s.sp.toNat - 856) 872 ∧
      Disjoint y.toNat 32 (s.sp.toNat - 856) 872 ∧ Disjoint m.toNat 32 (s.sp.toNat - 856) 872 ∧
      (z = m ∨ z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat) ∧
      (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
      (z = y ∨ z.toNat + 32 ≤ y.toNat ∨ y.toNat + 32 ≤ z.toNat) ∧
      ((s.regs 28).toNat + 24 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 28).toNat + 16)) :=
  ⟨ret, s0, z, x, x, x, hret, setup, hpre⟩

end Witness

end Fv256.Arm64.AddModMain
