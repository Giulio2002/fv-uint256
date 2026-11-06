import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecF
import Fv256.Arm64.SummaryEnsures
import Fv256.Arm64.SqrtEntry
import Fv256.Arm64.CodeIn

/-!
# `(*uint256.Int).Sqrt(x *Int) *Int` (arm64): `z = ⌊√x⌋`

**Documented behaviour.** "Sqrt sets z to ⌊√x⌋, the largest integer such that z² ≤ x, and returns z."

**Guarantee.** For all pointers `z` (receiver, `X0`) and `x` (`X1`) (they may be equal or overlap arbitrarily), the 32 bytes at `z`
writable, those at `x` readable (below `2^48`), outside the stack window `[SP-488, SP+24)`, a stack with room for the frames of `Sqrt` and
its callees (`Lsh`, `Rsh`, `udivrem`) (`StackOK s 488 24`, `SP >= 488`) and the stack-growth checks passing (`GuardOK s 448`): the call
returns (no fault, no panic, no division by zero), obeys the ABI, returns `z` in `X0`, the number at `z` afterwards is the integer
square root of the number at `x` before the call (`Fv256.F.IsSqrt`), and nothing changes outside `z[0..32)` and the window.
The proof is the library summary `Fv256.Arm64.SqrtSum.sqrt_summary` over `Fv256.Arm64.SqrtProg.program` (shared with `ISqrt`).

**Non-vacuity.** `Witness.nonvacuous`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Sqrt

set_option maxRecDepth 200000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.SqrtProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

theorem hentry : Fv256.Arm64.SqrtSum.sqrtEntry = Extracted.entry := rfl

theorem sqrt_summary_ex : Summary Extracted.program Extracted.entry Fv256.Arm64.SqrtSum.SqPre Fv256.Arm64.SqrtSum.PostSq := by
  have h1 := Janus.Contracts.EqHashModel.Summary.of_codeIn hcLib Fv256.Arm64.SqrtSum.sqrt_summary
  rw [hentry] at h1
  exact h1

abbrev Pre (z x : BitVec 64) : State → Prop :=
  fun s => GuardOK s 448 ∧ StackOK s 488 24 ∧ 488 ≤ s.sp.toNat ∧
    ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 488 ∨ s.sp.toNat + 24 ≤ (s.regs 28).toNat + 16) ∧
    Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧
    Disjoint z.toNat 32 (s.sp.toNat - 488) 512 ∧ Disjoint x.toNat 32 (s.sp.toNat - 488) 512

theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x] (Pre z x)
      (fun s s' => s'.regs 0 = z ∧ Fv256.F.IsSqrt (val256 s.mem x.toNat) (val256 s'.mem z.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 488, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 24)]) := by
  refine Fv256.Arm64.SummaryEnsures.ensures_of_summary _ _ sqrt_summary_ex ?_ ?_
  · intro ret hret s hsu ⟨hg, hs, hsp, hgw, ⟨hz, hz'⟩, ⟨hx, hx'⟩, hdz, hdx⟩
    have h30 : s.regs 30 = BitVec.ofNat 64 ret := by
      have := hsu.lr; exact this
    have h0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have h1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    rw [h30, h0, h1]
    have ha := hret.aligned
    have hu := hret.user
    refine ⟨?_, ?_, hg, hs, hsp, ?_, hz', hz, hx', hx, ?_, ?_⟩
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · unfold Apart; omega
    · simp only [Disjoint] at hdz; unfold Apart; omega
    · simp only [Disjoint] at hdx; unfold Apart; omega
  · intro ret hret s hsu ⟨hg, hs, hsp, hgw, ⟨hz, hz'⟩, ⟨hx, hx'⟩, hdz, hdx⟩ s' ⟨hpc, hsp2, h0, h18, h28, h29, h30, hv, hf⟩
    have e0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have e1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    rw [e0, e1] at hv
    rw [e0] at hf h0
    exact ⟨⟨hsp2, h28, h29, h18⟩, h0, hv, hf⟩

namespace Witness

open Janus.Contracts.EqHashModel

def retW : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def zp : Nat := 0x30800
def xp : Nat := 0x30900

def zW : BitVec 64 := BitVec.ofNat 64 zp
def xW : BitVec 64 := BitVec.ofNat 64 xp

def s0 : State :=
  { regs := fun i => if i = 0 then zW else if i = 1 then xW
      else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 sp0 - 8#64
      else if i = 30 then BitVec.ofNat 64 retW else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, [⟨sp0 - 488, 512, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 32, true⟩, ⟨xp, 32, false⟩]⟩ }

set_option maxRecDepth 200000 in
theorem hretW : RetAddr Extracted.program retW := RetAddr.of_check (by decide)

theorem setupW : CallSetup (Extracted.program.withExit retW) Extracted.entry [zW, xW] s0 :=
  ⟨rfl, rfl, by
    intro r h
    match r, h with
    | 0, _ => rfl
    | 1, _ => rfl⟩

set_option maxRecDepth 100000 in
theorem hpreW : Pre zW xW s0 := by
  refine ⟨by unfold GuardOK; decide, by unfold StackOK; decide, by decide, by decide,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_⟩ <;>
    (unfold Disjoint; decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧ Pre z x s :=
  ⟨retW, s0, zW, xW, hretW, setupW, hpreW⟩

end Witness

end Fv256.Arm64.Sqrt
