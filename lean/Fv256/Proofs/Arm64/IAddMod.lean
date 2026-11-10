import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Arm64.SummaryEnsures
import Fv256.Proofs.Arm64.AddMod
import Fv256.Proofs.Arm64.CodeIn
import Fv256.Proofs.Common.GrabTac

/-!
# `(*uint256.Int).IAddMod(x, m *Int) *Int` (arm64): in place, `z = (z + x) mod m`

**Documented behaviour.** `IAddMod` is `z.AddMod(z, x, m)`: "AddMod sets z to the sum ( x+y ) mod m, and returns z. If m == 0, z is set to 0."

**Guarantee.** For all pointers `z` (receiver, `X0`), `x` (`X1`), `m` (`X2`) with the 32 bytes at `z` writable, those at `x` and `m` readable
(all below `2^48`), none overlapping the callee window `[SP-904, SP-32)` (the frames of `IAddMod` and of the `AddMod` it calls), `z` equal to or
disjoint from `x` and from `m`, the stack-growth checks of both falling through (`GuardOK s 864`), the read-only data of the binary loaded and
`stackguard0` not overlapping `z`: the call returns (no fault, no panic), obeys the ABI, returns `z` in `X0`, the number at `z` afterwards is
`Fv256.F.addmodSpec` of the numbers at `z`, `x`, `m` before the call, and nothing changes outside `z[0..32)` and the window. The callee is used
through the Extracted-free library summary `Fv256.Arm64.AddMod.addmod_summary`.

**Non-vacuity.** `Witness.nonvacuous`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.IAddMod

set_option maxRecDepth 200000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.AddModProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

theorem hdata : Extracted.program.data = Fv256.Arm64.AddModProg.program.data := rfl

theorem hdl (m : Janus.Arm64.Memory) : Extracted.program.DataLoaded m ↔ Fv256.Arm64.AddModProg.program.DataLoaded m := by
  unfold Program.DataLoaded; rw [hdata]

/-- the library summary moved to this extraction, with the postcondition spelled out -/
theorem addmod_ext : Summary Extracted.program Fv256.Arm64.AddModProg.entry Fv256.Arm64.AddModSeg.PreS
    (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
      s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
      s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.addmodSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32)
        (s.mem.readLE (s.regs 3).toNat 32) ∧
      MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 856, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 16)]) :=
  Janus.Contracts.EqHashModel.Summary.of_codeIn hcLib Fv256.Arm64.AddMod.addmod_summary

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem iaddmod_summary : Summary Extracted.program Extracted.entry
    (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 864 ∧
        s.sp.toNat % 16 = 0 ∧ 904 ≤ s.sp.toNat ∧ s.sp.toNat ≤ 2 ^ 48 ∧ s.mem.accessible (s.sp.toNat - 904) 872 true = true ∧
        Extracted.program.DataLoaded s.mem ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 904 ∨ s.sp.toNat - 32 ≤ (s.regs 28).toNat + 16) ∧
        (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
        (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
        (s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧
        ((s.regs 0).toNat + 32 ≤ s.sp.toNat - 904 ∨ s.sp.toNat - 32 ≤ (s.regs 0).toNat) ∧
        ((s.regs 1).toNat + 32 ≤ s.sp.toNat - 904 ∨ s.sp.toNat - 32 ≤ (s.regs 1).toNat) ∧
        ((s.regs 2).toNat + 32 ≤ s.sp.toNat - 904 ∨ s.sp.toNat - 32 ≤ (s.regs 2).toNat) ∧
        (s.regs 0 = s.regs 2 ∨ (s.regs 0).toNat + 32 ≤ (s.regs 2).toNat ∨ (s.regs 2).toNat + 32 ≤ (s.regs 0).toNat) ∧
        (s.regs 0 = s.regs 1 ∨ (s.regs 0).toNat + 32 ≤ (s.regs 1).toNat ∨ (s.regs 1).toNat + 32 ≤ (s.regs 0).toNat) ∧
        ((s.regs 28).toNat + 24 ≤ (s.regs 0).toNat ∨ (s.regs 0).toNat + 32 ≤ (s.regs 28).toNat + 16))
    (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.addmodSpec (s.mem.readLE (s.regs 0).toNat 32) (s.mem.readLE (s.regs 1).toNat 32)
          (s.mem.readLE (s.regs 2).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 904, s.sp.toNat - 32)]) := by
  intro s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hdlE, hgw, hzb, hza, hxb, hxa, hmb, hma, hdz, hdx, hdm, hzm, hzx, hgz⟩
  have hdlA := (hdl _).1 hdlE
  janus_run calls [addmod_ext]
  grab_const Fv256.F.addmodSpec as hv
  grab_frame 856 as hfr
  refine ⟨hv, ?_⟩
  have hM0 : MemFrame s.mem ((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 (BitVec.toNat (s.regs 30))).writeLE
      (BitVec.toNat s.sp - 56) 8 (BitVec.toNat (s.regs 29)))
      [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 904, s.sp.toNat - 32)] :=
    ((MemFrame.refl s.mem _).writeLE _ (r := (s.sp.toNat - 904, s.sp.toNat - 32)) (by simp) (by dsimp only; omega)
      (by dsimp only; omega)).writeLE _ (r := (s.sp.toNat - 904, s.sp.toNat - 32)) (by simp) (by dsimp only; omega)
      (by dsimp only; omega)
  exact hM0.trans hfr (fun x n hx => by simp only [Outside, and_true] at hx ⊢; omega)


theorem correctness_proof (z x m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, m]
      (fun s => GuardOK s 864 ∧ s.sp.toNat % 16 = 0 ∧ 904 ≤ s.sp.toNat ∧ s.sp.toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (s.sp.toNat - 904) 872 true = true ∧ Extracted.program.DataLoaded s.mem ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 904 ∨ s.sp.toNat - 32 ≤ (s.regs 28).toNat + 16) ∧
        Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem m false ∧
        Disjoint z.toNat 32 (s.sp.toNat - 904) 872 ∧ Disjoint x.toNat 32 (s.sp.toNat - 904) 872 ∧
        Disjoint m.toNat 32 (s.sp.toNat - 904) 872 ∧
        (z = m ∨ z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat) ∧
        (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 24 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 28).toNat + 16))
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Fv256.F.addmodSpec (val256 s.mem z.toNat) (val256 s.mem x.toNat) (val256 s.mem m.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 904, s.sp.toNat - 32)]) := by
  refine Fv256.Arm64.SummaryEnsures.ensures_of_summary _ _ iaddmod_summary ?_ ?_
  · intro ret hret s hsu ⟨hg, hsal, hsb, hsc, hsw, hdata, hgw, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hm, hm'⟩, hdz, hdx, hdm, hzm, hzx, hgz⟩
    have h30 : s.regs 30 = BitVec.ofNat 64 ret := by
      have := hsu.lr; exact this
    have h0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have h1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    have h2 : s.regs 2 = m := by have := hsu.args 2 (by simp); simpa using this
    rw [h30, h0, h1, h2]
    have ha := hret.aligned
    have hu := hret.user
    refine ⟨?_, ?_, hg, hsal, hsb, hsc, hsw, hdata, hgw, hz', hz, hx', hx, hm', hm, ?_, ?_, ?_, hzm, hzx, hgz⟩
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [Disjoint] at hdz; omega
    · simp only [Disjoint] at hdx; omega
    · simp only [Disjoint] at hdm; omega
  · intro ret hret s hsu ⟨hg, hsal, hsb, hsc, hsw, hdata, hgw, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hm, hm'⟩, hdz, hdx, hdm, hzm, hzx, hgz⟩ s' ⟨hpc, hsp, h0, h18, h28, h29, h30, hv, hf⟩
    have e0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have e1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    have e2 : s.regs 2 = m := by have := hsu.args 2 (by simp); simpa using this
    rw [e0, e1, e2] at hv
    rw [e0] at hf h0
    refine ⟨⟨hsp, h28, h29, h18⟩, ?_, ?_, hf⟩
    · exact h0
    · exact hv

namespace Wit

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
  { regs := fun i => if i = 0 then z else if i = 1 then x else if i = 2 then x
      else if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 904, 872, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, true⟩] ++ dregs⟩ }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, x] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hpre : GuardOK s0 864 ∧ s0.sp.toNat % 16 = 0 ∧ 904 ≤ s0.sp.toNat ∧ s0.sp.toNat ≤ 2 ^ 48 ∧
    s0.mem.accessible (s0.sp.toNat - 904) 872 true = true ∧ Extracted.program.DataLoaded s0.mem ∧
    ((s0.regs 28).toNat + 24 ≤ s0.sp.toNat - 904 ∨ s0.sp.toNat - 32 ≤ (s0.regs 28).toNat + 16) ∧
    Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧ Ptr32 s0.mem x false ∧
    Disjoint z.toNat 32 (s0.sp.toNat - 904) 872 ∧ Disjoint x.toNat 32 (s0.sp.toNat - 904) 872 ∧
    Disjoint x.toNat 32 (s0.sp.toNat - 904) 872 ∧
    (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
    (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
    ((s0.regs 28).toNat + 24 ≤ z.toNat ∨ z.toNat + 32 ≤ (s0.regs 28).toNat + 16) := by
  refine ⟨by unfold GuardOK; decide, by decide, by decide, by decide, by decide, dataLoaded, by decide,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_,
    by decide, by decide, by decide⟩ <;>
    (unfold Disjoint; decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, m] s ∧
    (GuardOK s 864 ∧ s.sp.toNat % 16 = 0 ∧ 904 ≤ s.sp.toNat ∧ s.sp.toNat ≤ 2 ^ 48 ∧
      s.mem.accessible (s.sp.toNat - 904) 872 true = true ∧ Extracted.program.DataLoaded s.mem ∧
      ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 904 ∨ s.sp.toNat - 32 ≤ (s.regs 28).toNat + 16) ∧
      Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem m false ∧
      Disjoint z.toNat 32 (s.sp.toNat - 904) 872 ∧ Disjoint x.toNat 32 (s.sp.toNat - 904) 872 ∧
      Disjoint m.toNat 32 (s.sp.toNat - 904) 872 ∧
      (z = m ∨ z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat) ∧
      (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
      ((s.regs 28).toNat + 24 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 28).toNat + 16)) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Fv256.F.addmodSpec (val256 s.mem z.toNat) (val256 s.mem x.toNat) (val256 s.mem m.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 904, s.sp.toNat - 32)] :=
  ⟨ret, s0, z, x, x, hret, setup, hpre,
    correctness_proof z x x ret hret s0 setup hpre⟩

end Wit

end Fv256.Arm64.IAddMod
