import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.SpecB2
import Fv256.Proofs.Common.UtilB2
import Fv256.Proofs.Amd64.SDivSum
import Fv256.Proofs.Common.CodeIn
import Fv256.Proofs.Common.SDivProg

/-!
# `(*uint256.Int).ISDiv(x *Int) *Int` (amd64): in place, `z = z / x`, and `0` when `x = 0`

**Documented behaviour.** `ISDiv` is `z.Div(z, x)`: "Div sets z to the quotient x/y for returns z. If y == 0, z is set to 0."

**Guarantee.** For all pointers `z` (receiver, `RAX`) and `x` (`RBX`) (they may overlap arbitrarily: `Div` reads every input limb
before it writes `z`), and every Go call in which the stack-growth checks of `ISDiv` and of the `Div` it calls fall through
(`StackGuardOK s 0x238`), the window `[RSP-0x288, RSP+0x10)` is writable, the 32 bytes at `z` are writable, those at `x` readable
(all below `2^48`), neither overlaps the window, and the goroutine's `stackguard0` word is outside the window: the call returns
(no fault, no panic, no `#DE`), obeys the ABI, returns `z` in `RAX`, the number at `z` afterwards is `Fv256.B.sdivSpec` of the numbers
at `z` and `x` before the call (`z / x`, or `0` when `x = 0`), and no byte outside `z[0..32)` and the window changes (`MemFrame`).
The callee is used through the verified summary `Fv256.Amd64.SDivSum.sdiv_summary`.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.ISDiv

set_option maxRecDepth 100000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn64 Fv256.SDivProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x]
      (fun s => StackGuardOK s 0x238 ∧ 0x290 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x288 0x10 ∧ Buffer s z 32 true ∧
        Buffer s x 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x288 ∨ (s.regs regSP).toNat + 0x10 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x288 ∨ (s.regs regSP).toNat + 0x10 ≤ x.toNat) ∧
        ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x288 ∨ (s.regs regSP).toNat + 0x10 ≤ (s.regs regG).toNat + 16))
      (fun s s' => s'.regs 0 = z ∧ valueAt s' z 32 = Fv256.B.sdivSpec (valueAt s z 32) (valueAt s x 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x288, (s.regs regSP).toNat + 0x10)]) := by
  intro ret hret s hs ⟨hg, hsp, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, hdz, hdx, hdg⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hdx hsp
  simp only [valueAt]
  janus64_run [Util.readLE_32] calls [Fv256.CodeIn.lib_summary hcLib Fv256.Amd64.SDivSum.sdiv_summary]
  refine ⟨by assumption, MemFrame.trans (rs := [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x288, (s.regs regSP).toNat + 0x10)]) ?_ ‹MemFrame _ _ _› ?_⟩
  · exact ((MemFrame.refl _ _).writeLE_inRanges _ ⟨((s.regs regSP).toNat - 0x288, (s.regs regSP).toNat + 0x10), by simp, by simp only [regSP]; omega, by simp only [regSP]; omega⟩).writeLE_inRanges _
      ⟨((s.regs regSP).toNat - 0x288, (s.regs regSP).toNat + 0x10), by simp, by simp only [regSP]; omega, by simp only [regSP]; omega⟩
  · intro a n hh
    simp only [outside_cons, outside_nil, and_true, regSP] at hh ⊢
    omega

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

theorem hpre : StackGuardOK s0 0x238 ∧ 0x290 ≤ (s0.regs regSP).toNat ∧ StackWritable s0 0x288 0x10 ∧ Buffer s0 z 32 true ∧
    Buffer s0 x 32 false ∧
    (z.toNat + 32 ≤ (s0.regs regSP).toNat - 0x288 ∨ (s0.regs regSP).toNat + 0x10 ≤ z.toNat) ∧
    (x.toNat + 32 ≤ (s0.regs regSP).toNat - 0x288 ∨ (s0.regs regSP).toNat + 0x10 ≤ x.toNat) ∧
    ((s0.regs regG).toNat + 24 ≤ (s0.regs regSP).toNat - 0x288 ∨ (s0.regs regSP).toNat + 0x10 ≤ (s0.regs regG).toNat + 16) :=
  ⟨⟨by decide, by decide, by decide⟩, by unfold regSP; decide, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, by unfold regSP; decide, by unfold regSP; decide, by unfold regSP regG; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧
    (StackGuardOK s 0x238 ∧ 0x290 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x288 0x10 ∧ Buffer s z 32 true ∧
      Buffer s x 32 false ∧
      (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x288 ∨ (s.regs regSP).toNat + 0x10 ≤ z.toNat) ∧
      (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x288 ∨ (s.regs regSP).toNat + 0x10 ≤ x.toNat) ∧
      ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x288 ∨ (s.regs regSP).toNat + 0x10 ≤ (s.regs regG).toNat + 16)) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧ valueAt s' z 32 = Fv256.B.sdivSpec (valueAt s z 32) (valueAt s x 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x288, (s.regs regSP).toNat + 0x10)] :=
  ⟨ret, s0, z, x, hret, setup, hpre,
    correctness z x ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ valueAt s' z 32 = 0 := by
  refine (correctness z x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  simp only [valueAt, Fv256.B.sdivSpec, Fv256.B.divSpec, Fv256.Spec.abs, Fv256.Spec.neg]
  decide

end Witness

end Fv256.Amd64.ISDiv
