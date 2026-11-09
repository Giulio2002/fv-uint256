import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.SpecB2
import Fv256.Proofs.Common.UtilB2
import Fv256.Proofs.Amd64.UdivremA
import Fv256.Proofs.Amd64.UdivremK
import Fv256.Proofs.Amd64.UdivremL
import Fv256.Proofs.Common.CodeIn
import Fv256.Proofs.Common.DivProg
import Fv256.Proofs.Amd64.DivSum

/-!
# `(*uint256.Int).SDiv(x, y *Int) *Int` (amd64): signed quotient (truncated toward zero), `0` when `y = 0`

**Guarantee.** For all pointers `z` (receiver, `RAX`), `x` (`RBX`), `y` (`RCX`) (any overlap among the three is allowed), and every Go call
in which the stack-growth checks fall through (`StackGuardOK s 0x210`: `SDiv`, its callee `Div` and `Div`'s callee `udivrem`), the window
`[RSP-0x260, RSP+0x10)` is writable, `z` writable, `x`, `y` readable (below `2^48`), none overlapping the window, the goroutine's
`stackguard0` word outside the window: the call returns (no fault, no panic), obeys the ABI, returns `z`, and the number at `z` is
`Fv256.B.sdivSpec` of the numbers at `x` and `y` before the call; no byte outside `z[0..32)` and the window changes (`MemFrame`).
The proof uses the verified summary of `Div` (proved in this file for this extraction) as the callee.

**Non-vacuity.** `Witness.nonvacuous`, `Witness.returns` (a concrete call returns `0`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SDiv

set_option maxRecDepth 100000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn64 Fv256.DivProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

open Fv256.Amd64.DivSum

namespace Local
open Fv256.B

theorem abs_zero : Fv256.Spec.abs 0 = 0 := by simp [Fv256.Spec.abs]
theorem neg_zero : Fv256.Spec.neg 0 = 0 := by simp [Fv256.Spec.neg, Fv256.Spec.W]

theorem sdivSpec_x0 (x y : Nat) (h : x = 0) : sdivSpec x y = 0 := by
  subst h; unfold sdivSpec; simp [abs_zero, neg_zero, divSpec_zero_left]

theorem sdivSpec_y0 (x y : Nat) (h : y = 0) : sdivSpec x y = 0 := by
  subst h; unfold sdivSpec; simp [abs_zero, neg_zero, divSpec_zero_right]

theorem sdivSpec_zl (y : Nat) : sdivSpec 0 y = 0 := sdivSpec_x0 0 y rfl
theorem sdivSpec_zr (x : Nat) : sdivSpec x 0 = 0 := sdivSpec_y0 x 0 rfl

end Local

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
set_option profiler true in
set_option profiler.threshold 5000 in
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => StackGuardOK s 0x210 ∧ 0x268 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x260 0x10 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x260 ∨ (s.regs regSP).toNat + 0x10 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x260 ∨ (s.regs regSP).toNat + 0x10 ≤ x.toNat) ∧
        (y.toNat + 32 ≤ (s.regs regSP).toNat - 0x260 ∨ (s.regs regSP).toNat + 0x10 ≤ y.toNat) ∧
        ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x260 ∨ (s.regs regSP).toNat + 0x10 ≤ (s.regs regG).toNat + 16))
      (fun s s' => s'.regs 0 = z ∧ valueAt s' z 32 = Fv256.B.sdivSpec (valueAt s x 32) (valueAt s y 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x260, (s.regs regSP).toNat + 0x10)]) := by
  intro ret hret s hs ⟨hg, hsp, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, hdz, hdx, hdy, hdg⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hdx hdy hsp
  simp only [valueAt]
  have hx0 := Util.readLE8_lt s.mem x.toNat
  have hx1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have hx2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have hx3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hy0 := Util.readLE8_lt s.mem y.toNat
  have hy1 := Util.readLE8_lt s.mem (y.toNat + 8)
  have hy2 := Util.readLE8_lt s.mem (y.toNat + 16)
  have hy3 := Util.readLE8_lt s.mem (y.toNat + 24)
  janus64_run [Util.msb_m1, Util.msb_0, Util.msb_1, Util.readLE_32, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff] calls [Fv256.CodeIn.lib_summary hcLib Fv256.Amd64.DivSum.div_summary]
  all_goals (first | (exfalso; omega) | skip)
  all_goals (refine ⟨?_, ?_⟩)
  all_goals (first | janus_frame | skip)
  all_goals (first
    | (simp only [Local.sdivSpec_zl, Local.sdivSpec_zr])
    | skip)
  all_goals (
    have nx := Util.neg_chain _ _ _ _ hx0 hx1 hx2 hx3
    have ny := Util.neg_chain _ _ _ _ hy0 hy1 hy2 hy3
    have nz := Util.neg_chain _ _ _ _ (Util.readLE8_lt s'.mem z.toNat) (Util.readLE8_lt s'.mem (z.toNat + 8))
      (Util.readLE8_lt s'.mem (z.toNat + 16)) (Util.readLE8_lt s'.mem (z.toNat + 24))
    simp only [nx, ny, nz, Fv256.B.divSpec_zero_left, Fv256.B.divSpec_zero_right] at *
    rw [Fv256.B.sdivSpec]
    simp only [Fv256.Spec.abs, Fv256.Spec.neg, Fv256.Spec.W, Nat.reducePow]
    simp (disch := omega) only [if_pos, if_neg, Fv256.B.divSpec_zero_left, Fv256.B.divSpec_zero_right]
    omega)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then x else if i = 1 then x
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackGuardOK s0 0x210 ∧ 0x268 ≤ (s0.regs regSP).toNat ∧ StackWritable s0 0x260 0x10 ∧ Buffer s0 z 32 true ∧
    Buffer s0 x 32 false ∧ Buffer s0 x 32 false ∧
    (z.toNat + 32 ≤ (s0.regs regSP).toNat - 0x260 ∨ (s0.regs regSP).toNat + 0x10 ≤ z.toNat) ∧
    (x.toNat + 32 ≤ (s0.regs regSP).toNat - 0x260 ∨ (s0.regs regSP).toNat + 0x10 ≤ x.toNat) ∧
    (x.toNat + 32 ≤ (s0.regs regSP).toNat - 0x260 ∨ (s0.regs regSP).toNat + 0x10 ≤ x.toNat) ∧
    ((s0.regs regG).toNat + 24 ≤ (s0.regs regSP).toNat - 0x260 ∨ (s0.regs regSP).toNat + 0x10 ≤ (s0.regs regG).toNat + 16) :=
  ⟨⟨by decide, by decide, by decide⟩, by unfold regSP; decide, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by unfold regSP; decide, by unfold regSP; decide, by unfold regSP; decide,
    by unfold regSP regG; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧
    (StackGuardOK s 0x210 ∧ 0x268 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x260 0x10 ∧ Buffer s z 32 true ∧
      Buffer s x 32 false ∧ Buffer s y 32 false ∧
      (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x260 ∨ (s.regs regSP).toNat + 0x10 ≤ z.toNat) ∧
      (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x260 ∨ (s.regs regSP).toNat + 0x10 ≤ x.toNat) ∧
      (y.toNat + 32 ≤ (s.regs regSP).toNat - 0x260 ∨ (s.regs regSP).toNat + 0x10 ≤ y.toNat) ∧
      ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x260 ∨ (s.regs regSP).toNat + 0x10 ≤ (s.regs regG).toNat + 16)) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧ valueAt s' z 32 = Fv256.B.sdivSpec (valueAt s x 32) (valueAt s y 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x260, (s.regs regSP).toNat + 0x10)] :=
  ⟨ret, s0, z, x, x, hret, setup, hpre,
    correctness z x x ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ valueAt s' z 32 = 0 := by
  refine (correctness z x x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  simp only [valueAt, Fv256.B.sdivSpec, Fv256.B.divSpec, Fv256.Spec.abs, Fv256.Spec.neg]
  decide

end Witness

end Fv256.Amd64.SDiv
