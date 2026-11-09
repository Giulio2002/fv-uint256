import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Arm64.SummaryEnsures
import Fv256.Proofs.Arm64.ExpMain
import Fv256.Proofs.Arm64.CodeIn
import Fv256.Spec.Arm64.Exp

/-!
# `(*uint256.Int).Exp(base, exponent *Int) *Int` (arm64): `z = base ** exponent mod 2^256`

**Guarantee.** For all pointers `z` (receiver, `X0`), `b` (`X1`), `e` (`X2`) with the 32 bytes at `z` writable and those at `b`, `e` readable
(below `2^48`; they may be equal or overlap arbitrarily), outside the stack window `[SP-168, SP+40)`, a stack with room for the frame
(`StackOK s 168 40`, `SP >= 336`) and the stack-growth check passing, the rodata of the extraction loaded: the call returns (no fault, no
panic), obeys the ABI, returns `z` in `X0`, the number at `z` afterwards is `Fv256.F.expSpec` of the numbers at `b` and `e` before the call
(`b ^ e mod 2^256`), and nothing changes outside `z[0..32)` and the window.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Exp

set_option maxRecDepth 200000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ExpProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

theorem hdata : Extracted.program.data = Fv256.Arm64.ExpProg.program.data := rfl

theorem hdl (m : Janus.Arm64.Memory) : Extracted.program.DataLoaded m ↔ Fv256.Arm64.ExpProg.program.DataLoaded m := by
  unfold Program.DataLoaded; rw [hdata]

theorem hentry : Fv256.Arm64.ExpSum.expEntry = Extracted.entry := rfl

theorem exp_summary_ex : Summary Extracted.program Extracted.entry
    (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 32 ∧ StackOK s 168 40 ∧ 336 ≤ s.sp.toNat ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 168) 208 ∧
        (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
        (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
        (s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧
        Apart (s.regs 0).toNat 32 (s.sp.toNat - 168) 208 ∧ Apart (s.regs 1).toNat 32 (s.sp.toNat - 168) 208 ∧
        Apart (s.regs 2).toNat 32 (s.sp.toNat - 168) 208 ∧
        Extracted.program.DataLoaded s.mem)
    Fv256.Arm64.ExpMain.PostE := by
  have h1 := Janus.Contracts.EqHashModel.Summary.of_codeIn hcLib Fv256.Arm64.ExpMain.exp_summary
  rw [hentry] at h1
  intro s hpc hpre
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, hl⟩ := hpre
  exact h1 s hpc ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, (hdl _).1 hl⟩

theorem correctness (z b e : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, b, e] (Pre z b e)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Fv256.F.expSpec (val256 s.mem b.toNat) (val256 s.mem e.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 168, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32)]) := by
  refine Fv256.Arm64.SummaryEnsures.ensures_of_summary _ _ exp_summary_ex ?_ ?_
  · intro ret hret s hsu ⟨hg, hs, hsp, hgw, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, hdz, hdx, hdy, hdl⟩
    have h30 : s.regs 30 = BitVec.ofNat 64 ret := by
      have := hsu.lr; exact this
    have h0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have h1 : s.regs 1 = b := by have := hsu.args 1 (by simp); simpa using this
    have h2 : s.regs 2 = e := by have := hsu.args 2 (by simp); simpa using this
    rw [h30, h0, h1, h2]
    have ha := hret.aligned
    have hu := hret.user
    refine ⟨?_, ?_, hg, hs, hsp, ?_, hz', hz, hx', hx, hy', hy, ?_, ?_, ?_, hdl⟩
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · unfold Apart; omega
    · simp only [Disjoint] at hdz; unfold Apart; omega
    · simp only [Disjoint] at hdx; unfold Apart; omega
    · simp only [Disjoint] at hdy; unfold Apart; omega
  · intro ret hret s hsu ⟨hg, hs, hsp, hgw, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, hdz, hdx, hdy, hdl⟩ s' ⟨hpc, hsp2, h0, h18, h28, h29, h30, hv, hf⟩
    have e0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have e1 : s.regs 1 = b := by have := hsu.args 1 (by simp); simpa using this
    have e2 : s.regs 2 = e := by have := hsu.args 2 (by simp); simpa using this
    rw [e0, e1, e2] at hv
    rw [e0] at hf h0
    exact ⟨⟨hsp2, h28, h29, h18⟩, h0, hv, hf⟩

namespace Witness

open Janus.Contracts.EqHashModel

def retW : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def zp : Nat := 0x30800
def xp : Nat := 0x30900
def dat : DataSegment := Extracted.data.head!
def dlen : Nat := janus_eval% dat.bytes.length
def dbase : Nat := janus_eval% dat.base

def bytesW (a : Nat) : Byte :=
  if dbase ≤ a ∧ a < dbase + dlen then BitVec.ofNat 8 (dat.bytes.getD (a - dbase) 0) else 0

def zW : BitVec 64 := BitVec.ofNat 64 zp
def xW : BitVec 64 := BitVec.ofNat 64 xp

def s0 : State :=
  { regs := fun i => if i = 0 then zW else if i = 1 then xW else if i = 2 then xW
      else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 sp0 - 8#64
      else if i = 30 then BitVec.ofNat 64 retW else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytesW, [⟨sp0 - 168, 208, true⟩, ⟨g0, 0x100, false⟩, ⟨dbase, dlen, false⟩, ⟨zp, 32, true⟩, ⟨xp, 32, false⟩]⟩ }

set_option maxRecDepth 200000 in
theorem hretW : RetAddr Extracted.program retW := RetAddr.of_check (by decide)

theorem setupW : CallSetup (Extracted.program.withExit retW) Extracted.entry [zW, xW, xW] s0 :=
  ⟨rfl, rfl, by
    intro r h
    match r, h with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoadedW : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hpreW : Pre zW xW xW s0 := by
  refine ⟨by unfold GuardOK; decide, by unfold StackOK; decide, by decide, by decide,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_, dataLoadedW⟩ <;>
    (unfold Disjoint; decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z b e : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, b, e] s ∧ Pre z b e s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Fv256.F.expSpec (val256 s.mem b.toNat) (val256 s.mem e.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 168, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32)] :=
  ⟨retW, s0, zW, xW, xW, hretW, setupW, hpreW,
    correctness zW xW xW retW hretW s0 setupW hpreW⟩

end Witness

end Fv256.Arm64.Exp
