import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Common.AddModProg
import Fv256.Proofs.Amd64.AddModSum
import Fv256.Proofs.Amd64.IAddModCore
import Fv256.Spec.Amd64.IAddMod

/-!
# `(*uint256.Int).IAddMod(x, m *Int) *Int` (amd64): in place, `z = (z + x) mod m`

**Documented behaviour.** `IAddMod` is `z.AddMod(z, x, m)`: "AddMod sets z to the sum ( x+y ) mod m, and returns z. If m == 0, z is set to 0."

**Guarantee.** For all pointers `z` (receiver, `RAX`), `x` (`RBX`), `m` (`RCX`), where `z` and `x`, `z` and `m` are equal or disjoint, and every Go call in which
the stack-growth checks of `IAddMod` and of the `AddMod` it calls fall through (`StackGuardOK s 0x330`), the window `[RSP-0x378, RSP+0x10)` is writable,
the 32 bytes at `z` are writable, those at `x` and `m` readable, none overlaps the window, `stackguard0` is outside the window and the rodata is loaded:
the call returns (no fault, no panic), obeys the ABI, returns `z` in `RAX`, the number at `z` afterwards is `Fv256.F.addmodSpec` of the numbers at `z`, `x`, `m` before the call,
and nothing outside `z[0..32)` and the window changes. The callee is used through the library summary `Fv256.Amd64.AddModSum.addmod_summary` over `Fv256.AddModProg.program`.

**Non-vacuity.** `Witness.nonvacuous`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.IAddMod

theorem correctness (z x m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, m] (Pre z x m)
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Fv256.F.addmodSpec (valueAt s z 32) (valueAt s x 32) (valueAt s m 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x378, (s.regs regSP).toNat + 0x10)]) :=
  Fv256.Amd64.IAddModCore.correctness Fv256.Amd64.AddModSum.addmod_summary z x m

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
def m : BitVec 64 := BitVec.ofNat 64 (zp + 64)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then x else if i = 1 then m
      else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 0x378, 0x378 + 0x10, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, true⟩] ++
      Extracted.program.data.map (fun d => ⟨d.base, d.bytes.length, false⟩)⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, m] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hpre : Pre z x m s0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, by unfold regSP; decide, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, dataLoaded⟩ <;>
    first | (unfold regSP regG; decide) | (unfold regSP; decide) | (unfold regG; decide) | decide

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, m] s ∧ Pre z x m s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        valueAt s' z 32 = Fv256.F.addmodSpec (valueAt s z 32) (valueAt s x 32) (valueAt s m 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x378, (s.regs regSP).toNat + 0x10)] :=
  ⟨ret, s0, z, x, m, hret, setup, hpre,
    correctness z x m ret hret s0 setup hpre⟩

end Witness

end Fv256.Amd64.IAddMod
