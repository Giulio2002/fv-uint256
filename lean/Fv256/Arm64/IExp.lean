import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecF
import Fv256.Arm64.SummaryEnsures
import Fv256.Arm64.ExpMain
import Fv256.Arm64.CodeIn

/-!
# `(*uint256.Int).IExp(exponent *Int) *Int` (arm64): in place, `z = z ** exponent mod 2^256`

**Documented behaviour.** `IExp` is `z.Exp(z, exponent)`: "IExp sets z = z**exponent mod 2**256, and returns z."

**Guarantee.** For all pointers `z` (receiver, `X0`) and `e` (`X1`) (they may be equal or overlap arbitrarily), the 32 bytes at `z` writable,
those at `e` readable (below `2^48`), outside the stack window `[SP-216, SP-8)`, a stack with room for the frames and the stack-growth
checks of `IExp` and `Exp` passing, the rodata loaded: the call returns (no fault, no panic), obeys the ABI, returns `z` in `X0`, the number
at `z` afterwards is `Fv256.F.expSpec` of the numbers at `z` and `e` before the call, and nothing changes outside `z[0..32)` and the window.
The callee is used through the verified summary `Fv256.Arm64.ExpMain.exp_summary`.

**Non-vacuity.** `Witness.nonvacuous`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.IExp

set_option maxRecDepth 200000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ExpProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

theorem hdl (m : Janus.Arm64.Memory) : Extracted.program.DataLoaded m ↔ Fv256.Arm64.ExpProg.program.DataLoaded m := by
  unfold Program.DataLoaded; exact Iff.rfl

theorem exp_ex : Summary Extracted.program Fv256.Arm64.ExpSum.expEntry
    (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 32 ∧ StackOK s 168 40 ∧ 336 ≤ s.sp.toNat ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 168) 208 ∧
        (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
        (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
        (s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧
        Apart (s.regs 0).toNat 32 (s.sp.toNat - 168) 208 ∧ Apart (s.regs 1).toNat 32 (s.sp.toNat - 168) 208 ∧
        Apart (s.regs 2).toNat 32 (s.sp.toNat - 168) 208 ∧
        Extracted.program.DataLoaded s.mem)
    (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.expSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 168, s.sp.toNat - 8),
          (s.sp.toNat + 8, s.sp.toNat + 32)]) := by
  have h1 := Janus.Contracts.EqHashModel.Summary.of_codeIn hcLib Fv256.Arm64.ExpMain.exp_summary
  intro s hpc hpre
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, hl⟩ := hpre
  have h2 := h1 s hpc ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, (hdl _).1 hl⟩
  unfold Fv256.Arm64.ExpMain.PostE at h2
  exact h2

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem iexp_summary_ex : Summary Extracted.program Extracted.entry
    (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 80 ∧ StackOK s 216 8 ∧ 384 ≤ s.sp.toNat ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 216) 208 ∧
        (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
        (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
        Apart (s.regs 0).toNat 32 (s.sp.toNat - 216) 208 ∧ Apart (s.regs 1).toNat 32 (s.sp.toNat - 216) 208 ∧
        Extracted.program.DataLoaded s.mem)
    (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.expSpec (s.mem.readLE (s.regs 0).toNat 32) (s.mem.readLE (s.regs 1).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 216, s.sp.toNat - 8)]) := by
  intro s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, ⟨hsal, hsb, hsc, hsw⟩, hsp, hdg, hzb, hza, hxb, hxa, hdz, hdx, hdl⟩
  janus_run [] calls [exp_ex]
  refine ⟨by janus_assumption, ?_⟩
  janus_frame

abbrev Pre (z e : BitVec 64) : State → Prop :=
  fun s => GuardOK s 80 ∧ StackOK s 216 8 ∧ 384 ≤ s.sp.toNat ∧
    ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 216 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
    Ptr32 s.mem z true ∧ Ptr32 s.mem e false ∧
    Disjoint z.toNat 32 (s.sp.toNat - 216) 208 ∧ Disjoint e.toNat 32 (s.sp.toNat - 216) 208 ∧ Extracted.program.DataLoaded s.mem

theorem correctness (z e : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, e] (Pre z e)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Fv256.F.expSpec (val256 s.mem z.toNat) (val256 s.mem e.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 216, s.sp.toNat - 8)]) := by
  refine Fv256.Arm64.SummaryEnsures.ensures_of_summary _ _ iexp_summary_ex ?_ ?_
  · intro ret hret s hsu ⟨hg, hs, hsp, hgw, ⟨hz, hz'⟩, ⟨hx, hx'⟩, hdz, hdx, hdl⟩
    have h30 : s.regs 30 = BitVec.ofNat 64 ret := by
      have := hsu.lr; exact this
    have h0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have h1 : s.regs 1 = e := by have := hsu.args 1 (by simp); simpa using this
    rw [h30, h0, h1]
    have ha := hret.aligned
    have hu := hret.user
    refine ⟨?_, ?_, hg, hs, hsp, ?_, hz', hz, hx', hx, ?_, ?_, hdl⟩
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · unfold Apart; omega
    · simp only [Disjoint] at hdz; unfold Apart; omega
    · simp only [Disjoint] at hdx; unfold Apart; omega
  · intro ret hret s hsu ⟨hg, hs, hsp, hgw, ⟨hz, hz'⟩, ⟨hx, hx'⟩, hdz, hdx, hdl⟩ s' ⟨hpc, hsp2, h0, h18, h28, h29, h30, hv, hf⟩
    have e0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have e1 : s.regs 1 = e := by have := hsu.args 1 (by simp); simpa using this
    rw [e0, e1] at hv
    rw [e0] at hf h0
    exact ⟨⟨hsp2, h28, h29, h18⟩, h0, hv, hf⟩

namespace Witness

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
  { regs := fun i => if i = 0 then zW else if i = 1 then xW
      else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 sp0 - 8#64
      else if i = 30 then BitVec.ofNat 64 retW else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytesW, [⟨sp0 - 216, 224, true⟩, ⟨g0, 0x100, false⟩, ⟨dbase, dlen, false⟩, ⟨zp, 32, true⟩, ⟨xp, 32, false⟩]⟩ }

set_option maxRecDepth 200000 in
theorem hretW : RetAddr Extracted.program retW := RetAddr.of_check (by decide)

theorem setupW : CallSetup (Extracted.program.withExit retW) Extracted.entry [zW, xW] s0 :=
  ⟨rfl, rfl, by
    intro r h
    match r, h with
    | 0, _ => rfl
    | 1, _ => rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoadedW : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hpreW : Pre zW xW s0 := by
  refine ⟨by unfold GuardOK; decide, by unfold StackOK; decide, by decide, by decide,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, dataLoadedW⟩ <;>
    (unfold Disjoint; decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z e : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, e] s ∧ Pre z e s :=
  ⟨retW, s0, zW, xW, hretW, setupW, hpreW⟩

end Witness

end Fv256.Arm64.IExp
