import Extracted
import Fv256.SpecF
import Fv256.CodeIn
import Fv256.Amd64.AddModSum
import Fv256.Amd64.EnsuresOfW

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.AddMod

abbrev Pre (z x y m : BitVec 64) : State → Prop :=
  fun s => StackGuardOK s 0x300 ∧ 0x380 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x348 0x28 ∧ Extracted.program.DataLoaded s.mem ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s m 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ x.toNat) ∧
        (y.toNat + 32 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ y.toNat) ∧
        (m.toNat + 32 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ m.toNat) ∧
        (z = m ∨ z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat) ∧
        (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
        (z = y ∨ z.toNat + 32 ≤ y.toNat ∨ y.toNat + 32 ≤ z.toNat) ∧
        ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ (s.regs regG).toNat + 16) ∧
        ((s.regs regG).toNat + 24 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs regG).toNat + 16)

set_option maxRecDepth 100000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn64 Fv256.AddModProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hdata : Extracted.program.data = Fv256.AddModProg.program.data := by decide

theorem hdl (m : Janus.Arm64.Memory) : Extracted.program.DataLoaded m ↔ Fv256.AddModProg.program.DataLoaded m := by
  unfold Program.DataLoaded; rw [hdata]

theorem hentry : Fv256.Amd64.AddModSum.addmodEntry = Extracted.entry := by decide

theorem hsumE :
    Summary Extracted.program Extracted.entry (fun s => Fv256.Amd64.AddModSpecS.AddPre Extracted.program s) Fv256.Amd64.AddModSpecS.AddPost := by
  have h1 := Fv256.CodeIn.lib_summary hcLib Fv256.Amd64.AddModSum.addmod_summary
  rw [hentry] at h1
  intro s hpc hpre
  obtain ⟨a, b, c, d, hl, rest⟩ := hpre
  exact h1 s hpc ⟨a, b, c, d, (hdl _).1 hl, rest⟩

theorem correctness (z x y m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, m] (Pre z x y m)
      (fun s s' => s'.regs 0 = z ∧ s'.mem.readLE z.toNat 32 = Fv256.F.addmodSpec (s.mem.readLE x.toNat 32) (s.mem.readLE y.toNat 32) (s.mem.readLE m.toNat 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x348, (s.regs regSP).toNat + 0x28)]) := by
  have := Fv256.Amd64.EnsuresOfW.ensures4w 0x380 0x348 0x300 0x28 (by decide) Fv256.F.addmodSpec hsumE z x y m
  exact this

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def zp : Nat := 0x30800

/-- return address in the word at `[SP]`; the rodata bytes of the extraction; everything else zero -/
def bytes (a : Nat) : Byte :=
  if a = sp0 + 2 then 0x20
  else match Extracted.program.data.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
    | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
    | none => 0

def z : BitVec 64 := BitVec.ofNat 64 zp
def x : BitVec 64 := BitVec.ofNat 64 (zp + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then x else if i = 1 then x else if i = 7 then x
      else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 0x348, 0x348 + 0x28, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, true⟩] ++
      Extracted.program.data.map (fun d => ⟨d.base, d.bytes.length, false⟩)⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, x, x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hpre : Pre z x x x s0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, by unfold regSP; decide, ⟨by decide, by decide, by decide⟩, dataLoaded,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | (unfold regSP regG; decide) | (unfold regSP; decide) | (unfold regG; decide) | decide

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y, m] s ∧ Pre z x y m s :=
  ⟨ret, s0, z, x, x, x, hret, setup, hpre⟩

end Witness

end Fv256.Amd64.AddMod
