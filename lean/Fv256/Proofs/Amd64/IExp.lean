import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.SpecB2
import Fv256.Proofs.Common.UtilB2
import Fv256.Proofs.Amd64.ExpMain
import Fv256.Proofs.Amd64.ExpSum
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Common.CodeIn
import Fv256.Proofs.Common.ExpProg
import Fv256.Spec.Amd64.IExp

/-!
# `(*uint256.Int).IExp(exponent *Int) *Int` (amd64): in place, `z = z ** exponent mod 2^256`

**Documented behaviour.** `IExp` is `z.Exp(z, exponent)`: "IExp sets z = z**exponent mod 2**256, and returns z."

**Guarantee.** For all pointers `z` (receiver, `RAX`) and `e` (`RBX`) (they may overlap arbitrarily), and every Go call in which the stack-growth
checks of `IExp` and of the `Exp` it calls fall through (`StackGuardOK s 0x48`), the window `[RSP-0xd0, RSP+0x10)` is writable, the 32 bytes at `z`
are writable, those at `e` readable (all below `2^48`), neither overlaps the window, the goroutine's `stackguard0` word is outside the window and
the rodata of the extraction is loaded: the call returns (no fault, no panic), obeys the ABI, returns `z` in `RAX`, the number at `z` afterwards is
`Fv256.F.expSpec` of the numbers at `z` and `e` before the call (`z^e mod 2^256`), and no byte outside `z[0..32)` and the window changes
(`MemFrame`). The callee is used through the verified summary `Fv256.Amd64.ExpMain.exp_summary`.

**Non-vacuity.** `Witness.nonvacuous`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.IExp

set_option maxRecDepth 100000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ExpProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

theorem hdata : Extracted.program.data = Fv256.ExpProg.program.data := rfl

theorem hdl (m : Janus.Arm64.Memory) : Extracted.program.DataLoaded m ↔ Fv256.ExpProg.program.DataLoaded m := by
  unfold Amd64.Program.DataLoaded; rw [hdata]

theorem hsumE :
    Summary Extracted.program Fv256.Amd64.ExpSum.expEntry
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
  intro s hpc hpre
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, hl⟩ := hpre
  exact h1 s hpc ⟨a, b, c, d, e, f, g, h, i, j, k, l, (hdl _).1 hl⟩


set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x] (Pre z x)
      (fun s s' => s'.regs 0 = z ∧ valueAt s' z 32 = Fv256.F.expSpec (valueAt s z 32) (valueAt s x 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0xd0, (s.regs regSP).toNat + 0x10)]) := by
  intro ret hret s hs ⟨hg, hsp, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, hdz, hdx, hdg, hdl⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hdx hsp
  simp only [valueAt]
  janus64_run [Util.readLE_32] calls [hsumE]
  refine ⟨by assumption, MemFrame.trans (rs := [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0xd0, (s.regs regSP).toNat + 0x10)]) ?_ ‹MemFrame _ _ _› ?_⟩
  · exact ((MemFrame.refl _ _).writeLE_inRanges _ ⟨((s.regs regSP).toNat - 0xd0, (s.regs regSP).toNat + 0x10), by simp, by simp only [regSP]; omega, by simp only [regSP]; omega⟩).writeLE_inRanges _
      ⟨((s.regs regSP).toNat - 0xd0, (s.regs regSP).toNat + 0x10), by simp, by simp only [regSP]; omega, by simp only [regSP]; omega⟩
  · intro a n hh
    simp only [outside_cons, outside_nil, and_true, regSP] at hh ⊢
    omega

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
  { regs := fun i => if i = 0 then z else if i = 3 then x
      else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 0xd0, 0xd0 + 0x10, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, true⟩] ++
      Extracted.program.data.map (fun d => ⟨d.base, d.bytes.length, false⟩)⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hpre : Pre z x s0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, by unfold regSP; decide, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_, dataLoaded⟩ <;>
    first | (unfold regSP regG; decide) | (unfold regSP; decide) | (unfold regG; decide) | decide

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧ Pre z x s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧ valueAt s' z 32 = Fv256.F.expSpec (valueAt s z 32) (valueAt s x 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0xd0, (s.regs regSP).toNat + 0x10)] :=
  ⟨ret, s0, z, x, hret, setup, hpre,
    correctness z x ret hret s0 setup hpre⟩


end Witness

end Fv256.Amd64.IExp
