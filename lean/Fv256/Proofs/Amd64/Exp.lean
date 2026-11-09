import Extracted
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Common.CodeIn
import Fv256.Proofs.Amd64.ExpMain
import Fv256.Proofs.Amd64.EnsuresOfW

/-!
# `(*uint256.Int).Exp(base, exponent *Int) *Int` (amd64): `z = base ** exponent mod 2^256`

Guarantee: for every call satisfying `PreRaw` (stack-growth check falls through, the window `[RSP-0xa8, RSP+0x20)` writable, the 32 bytes at `z`
writable, those at `base` and `exponent` readable, none overlapping the window, `stackguard0` outside the window, rodata loaded),
the call returns, obeys the ABI, returns `z` in `RAX`, the number at `z` afterwards is `Fv256.F.expSpec` of the numbers at `base`
and `exponent` before the call (`base^exponent mod 2^256`), and nothing outside `z[0..32)` and the window changes. `z`, `base`, `exponent` may overlap arbitrarily.
Non-vacuity: `Witness.nonvacuous`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Exp

/-- (proof-internal) the precondition in raw form; the readable statement is `Fv256/Amd64/Exp.lean` -/
abbrev PreRaw (z b e : BitVec 64) : State → Prop :=
  fun s => StackGuardOK s 0x20 ∧ 0x100 ≤ (s.regs regSP).toNat ∧ StackWritable s 0xa8 0x20 ∧ Buffer s z 32 true ∧
        Buffer s b 32 false ∧ Buffer s e 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ z.toNat) ∧
        (b.toNat + 32 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ b.toNat) ∧
        (e.toNat + 32 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ e.toNat) ∧
        ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ (s.regs regG).toNat + 16) ∧
        Extracted.program.DataLoaded s.mem

set_option maxRecDepth 100000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ExpProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

theorem hdata : Extracted.program.data = Fv256.ExpProg.program.data := rfl

theorem hdl (m : Janus.Arm64.Memory) : Extracted.program.DataLoaded m ↔ Fv256.ExpProg.program.DataLoaded m := by
  unfold Amd64.Program.DataLoaded; rw [hdata]

theorem hentry : Fv256.Amd64.ExpSum.expEntry = Extracted.entry := rfl

theorem hsumE :
    Summary Extracted.program Extracted.entry
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        0x100 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0x20 ∧ StackWritable s 0xa8 0x20 ∧ s.xmm 15 = 0 ∧
        Buffer s (s.regs 0) 32 true ∧ Buffer s (s.regs 3) 32 false ∧ Buffer s (s.regs 1) 32 false ∧
        ((s.regs 0).toNat + 32 ≤ (s.regs 4).toNat - 0xa8 ∨ (s.regs 4).toNat + 0x20 ≤ (s.regs 0).toNat) ∧
        ((s.regs 3).toNat + 32 ≤ (s.regs 4).toNat - 0xa8 ∨ (s.regs 4).toNat + 0x20 ≤ (s.regs 3).toNat) ∧
        ((s.regs 1).toNat + 32 ≤ (s.regs 4).toNat - 0xa8 ∨ (s.regs 4).toNat + 0x20 ≤ (s.regs 1).toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 0xa8 ∨ (s.regs 4).toNat + 0x20 ≤ (s.regs 14).toNat + 16) ∧
        Extracted.program.DataLoaded s.mem)
      (fun s s' => s'.regs 0 = s.regs 0 ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.expSpec (s.mem.readLE (s.regs 3).toNat 32) (s.mem.readLE (s.regs 1).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat - 0xa8, (s.regs 4).toNat + 0x20)]) := by
  have h1 := Fv256.CodeIn.lib_summary hcLib Fv256.Amd64.ExpMain.exp_summary
  rw [hentry] at h1
  intro s hpc hpre
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, hl⟩ := hpre
  exact h1 s hpc ⟨a, b, c, d, e, f, g, h, i, j, k, l, (hdl _).1 hl⟩

theorem correctness_proof (z b e : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, b, e] (PreRaw z b e)
      (fun s s' => s'.regs 0 = z ∧ valueAt s' z 32 = Fv256.F.expSpec (valueAt s b 32) (valueAt s e 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0xa8, (s.regs regSP).toNat + 0x20)]) :=
  Fv256.Amd64.EnsuresOfW.ensures3w 0x100 0xa8 0x20 0x20 (by decide) (by decide) Fv256.F.expSpec hsumE z b e

namespace Wit

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
    mem := ⟨bytes, [⟨sp0 - 0xa8, 0xa8 + 0x20, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, true⟩] ++
      Extracted.program.data.map (fun d => ⟨d.base, d.bytes.length, false⟩)⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hpre : PreRaw z x x s0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, by unfold regSP; decide, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_, ?_, dataLoaded⟩ <;>
    first | (unfold regSP regG; decide) | (unfold regSP; decide) | (unfold regG; decide) | decide

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z b e : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, b, e] s ∧ PreRaw z b e s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧ valueAt s' z 32 = Fv256.F.expSpec (valueAt s b 32) (valueAt s e 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0xa8, (s.regs regSP).toNat + 0x20)] :=
  ⟨ret, s0, z, x, x, hret, setup, hpre,
    correctness_proof z x x ret hret s0 setup hpre⟩

end Wit

end Fv256.Amd64.Exp
