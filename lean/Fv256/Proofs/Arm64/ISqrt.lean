import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Arm64.SummaryEnsures
import Fv256.Proofs.Arm64.SqrtEntry
import Fv256.Proofs.Arm64.CodeIn
import Fv256.Spec.Arm64.ISqrt

/-!
# `(*uint256.Int).ISqrt() *Int` (arm64): in place, `z = ⌊√z⌋`

**Documented behaviour.** `ISqrt` is `z.Sqrt(z)`: "Sqrt sets z to ⌊√x⌋, the largest integer such that z² ≤ x, and returns z."

**Guarantee.** For every pointer `z` (receiver, `X0`) with the 32 bytes at `z` writable (below `2^48`), outside the stack window
`[SP-520, SP+8)`, a stack with room for the frames of `ISqrt` and `Sqrt` (`StackOK s 520 8`, `SP >= 520`) and the stack-growth checks of
`ISqrt` and of the callees passing (`GuardOK s 480`): the call returns (no fault, no panic), obeys the ABI, returns `z` in `X0`, the number
at `z` afterwards is the integer square root of the number at `z` before the call (`Fv256.F.IsSqrt`), and nothing changes outside
`z[0..32)` and the window. The callee is used through the verified summary `Fv256.Arm64.SqrtSum.sqrt_summary`.

**Non-vacuity.** `Witness.nonvacuous`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.ISqrt

set_option maxRecDepth 200000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.SqrtProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

theorem sqrt_ex : Summary Extracted.program Fv256.Arm64.SqrtSum.sqrtEntry Fv256.Arm64.SqrtSum.SqPre
    (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
      s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
      Fv256.F.IsSqrt (s.mem.readLE (s.regs 1).toNat 32) (s'.mem.readLE (s.regs 0).toNat 32) ∧
      MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 488, s.sp.toNat - 8),
        (s.sp.toNat + 8, s.sp.toNat + 24)]) :=
  Janus.Contracts.EqHashModel.Summary.of_codeIn hcLib Fv256.Arm64.SqrtSum.sqrt_summary

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem isqrt_summary_ex : Summary Extracted.program Extracted.entry
    (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 480 ∧ StackOK s 520 8 ∧ 520 ≤ s.sp.toNat ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 520) 528 ∧
        (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
        Apart (s.regs 0).toNat 32 (s.sp.toNat - 520) 528)
    (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        Fv256.F.IsSqrt (s.mem.readLE (s.regs 0).toNat 32) (s'.mem.readLE (s.regs 0).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 520, s.sp.toNat)]) := by
  intro s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, ⟨hsal, hsb, hsc, hsw⟩, hsp, hdg, hzb, hza, hdz⟩
  have e32 : (s.sp - 32#64).toNat = s.sp.toNat - 32 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hal32 : (s.sp - 32#64).toNat % 16 = 0 := by omega
  janus_run [hal32, e32] calls [sqrt_ex]
  refine ⟨by janus_assumption, ?_⟩
  janus_frame

theorem correctness (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z] (Pre z)
      (fun s s' => s'.regs 0 = z ∧ Fv256.F.IsSqrt (val256 s.mem z.toNat) (val256 s'.mem z.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 520, s.sp.toNat)]) := by
  refine Fv256.Arm64.SummaryEnsures.ensures_of_summary _ _ isqrt_summary_ex ?_ ?_
  · intro ret hret s hsu ⟨hg, hs, hsp, hgw, ⟨hz, hz'⟩, hdz⟩
    have h30 : s.regs 30 = BitVec.ofNat 64 ret := by
      have := hsu.lr; exact this
    have h0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    rw [h30, h0]
    have ha := hret.aligned
    have hu := hret.user
    refine ⟨?_, ?_, hg, hs, hsp, ?_, hz', hz, ?_⟩
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · unfold Apart; omega
    · simp only [Disjoint] at hdz; unfold Apart; omega
  · intro ret hret s hsu ⟨hg, hs, hsp, hgw, ⟨hz, hz'⟩, hdz⟩ s' ⟨hpc, hsp2, h0, h18, h28, h29, h30, hv, hf⟩
    have e0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    rw [e0] at hv hf h0
    exact ⟨⟨hsp2, h28, h29, h18⟩, h0, hv, hf⟩

namespace Witness

open Janus.Contracts.EqHashModel

def retW : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def zp : Nat := 0x30800

def zW : BitVec 64 := BitVec.ofNat 64 zp

def s0 : State :=
  { regs := fun i => if i = 0 then zW
      else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 sp0 - 8#64
      else if i = 30 then BitVec.ofNat 64 retW else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, [⟨sp0 - 520, 528, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 32, true⟩]⟩ }

set_option maxRecDepth 200000 in
theorem hretW : RetAddr Extracted.program retW := RetAddr.of_check (by decide)

theorem setupW : CallSetup (Extracted.program.withExit retW) Extracted.entry [zW] s0 :=
  ⟨rfl, rfl, by
    intro r h
    match r, h with
    | 0, _ => rfl⟩

set_option maxRecDepth 100000 in
theorem hpreW : Pre zW s0 := by
  refine ⟨by unfold GuardOK; decide, by unfold StackOK; decide, by decide, by decide,
    ⟨by decide, by decide⟩, ?_⟩
  unfold Disjoint; decide

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s ∧ Pre z s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧ Fv256.F.IsSqrt (val256 s.mem z.toNat) (val256 s'.mem z.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 520, s.sp.toNat)] :=
  ⟨retW, s0, zW, hretW, setupW, hpreW,
    correctness zW retW hretW s0 setupW hpreW⟩

end Witness

end Fv256.Arm64.ISqrt
