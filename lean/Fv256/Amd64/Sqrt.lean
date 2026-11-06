import Extracted
import Fv256.Spec
import Fv256.SpecF
import Fv256.CodeIn
import Fv256.SqrtProg
import Fv256.Amd64.SqrtSummaryL
import Fv256.Amd64.EnsuresOfS

/-!
# `(*uint256.Int).Sqrt(x *Int) *Int` (amd64): `z = ⌊√x⌋`

**Documented behaviour.** "Sqrt sets z to ⌊√x⌋, the largest integer such that z² ≤ x, and returns z."

**Guarantee.** For all pointers `z` (receiver, `RAX`) and `x` (`RBX`), equal or disjoint, and every Go call in which the stack-growth
checks of `Sqrt` and of the callees it uses (`Lsh`, `Rsh`, `udivrem`) fall through (`StackGuardOK s 0x200`), the window
`[RSP-0x1f0, RSP+0x18)` is writable, the 32 bytes at `z` are writable, those at `x` readable (below `2^48`), neither overlaps the window, and
the goroutine's `stackguard0` word is outside the window: the call returns (no fault, no panic, no `#DE`), obeys the ABI, returns `z` in `RAX`, the
number at `z` afterwards is `⌊√⌋` of the number at `x` before the call (`Fv256.F.IsSqrt`), and no byte outside `z[0..32)` and the window changes.
The proof is the library summary `Fv256.Amd64.SqrtLib.sqrt_summary` over `Fv256.SqrtProg.program` (shared with `ISqrt`).

**Non-vacuity.** `Witness.nonvacuous`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Sqrt

abbrev Pre (z x : BitVec 64) : State → Prop :=
  fun s => StackGuardOK s 0x200 ∧ 0x280 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x1f0 0x18 ∧ Buffer s z 32 true ∧
    Buffer s x 32 false ∧
    (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x1f0 ∨ (s.regs regSP).toNat + 0x18 ≤ z.toNat) ∧
    (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x1f0 ∨ (s.regs regSP).toNat + 0x18 ≤ x.toNat) ∧
    (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
    ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x1f0 ∨ (s.regs regSP).toNat + 0x18 ≤ (s.regs regG).toNat + 16)

set_option maxRecDepth 100000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn64 Fv256.SqrtProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

theorem hentry : Fv256.Amd64.SqrtLib.sqrtEntry = Extracted.entry := rfl

theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x] (Pre z x)
      (fun s s' => s'.regs 0 = z ∧ Fv256.F.IsSqrt (valueAt s x 32) (valueAt s' z 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x1f0, (s.regs regSP).toNat + 0x18)]) := by
  have h1 := Fv256.CodeIn.lib_summary hcLib Fv256.Amd64.SqrtLib.sqrt_summary
  rw [hentry] at h1
  exact Fv256.Amd64.EnsuresOfS.ensures2s 0x280 0x1f0 0x200 0x18 (by decide) Fv256.F.IsSqrt h1 z x

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then x
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem hpre : Pre z x s0 :=
  ⟨⟨by decide, by decide, by decide⟩, by unfold regSP; decide, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, by unfold regSP; decide, by unfold regSP; decide, Or.inr (Or.inl (by decide)),
    by unfold regSP regG; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧ Pre z x s :=
  ⟨ret, s0, z, x, hret, setup, hpre⟩

end Witness

end Fv256.Amd64.Sqrt
