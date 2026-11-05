import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.SpecF
import Fv256.UtilF
import Fv256.UtilMDO
import Fv256.Arm64.SummaryEnsures
import Fv256.Arm64.UmulSum
import Fv256.Arm64.UdivremFinal
import Fv256.Arm64.ChainProg
import Fv256.Arm64.CodeIn

/-!
# `(*uint256.Int).MulDivOverflow(x, y, d *Int) (*Int, bool)` (arm64)

**Documented behaviour.** "MulDivOverflow calculates (x*y)/d with full precision, returns z and whether overflow occurred in
multiply process (result does not fit to 256-bit)". As recorded in UINT256-FINDINGS F-F2 the flag is set iff the quotient
`x*y/d` does not fit in 256 bits (not iff the product does), and a zero `x`, `y` or `d` gives `(0, false)`; the spec
(`Fv256.F.muldivSpec`, `Fv256.F.muldivOv`) follows the code and these conventions.

**Guarantee.** For all pointers `z` (`X0`), `x` (`X1`), `y` (`X2`), `d` (`X3`) (the 32 bytes at `z` writable, the others readable,
all below `2^48`, none overlapping the callee window `[SP-552, SP+40)`; they may overlap each other), the window writable,
the stack-growth checks falling through (`GuardOK s 512`): the call returns (no fault, no panic), obeys the ABI, returns `z` in
`X0`, returns in `X1` the flag as `0`/`1`, the number at `z` afterwards is `muldivSpec` of the numbers at `x`, `y`, `d` before the
call, and nothing changes outside `z[0..32)` and the window. Callees are used through the verified library summaries
`UmulSum.umul_summary` (`UmulProg`) and `UdivremFinal.udivrem_nil_L_final` (`ChainProg`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.MulDivOverflow

set_option maxRecDepth 200000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ChainProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 200000 in
theorem hcUmul : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.UmulProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem mdo_summary : Summary Extracted.program Extracted.entry
    (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 512 ∧
        s.sp.toNat % 16 = 0 ∧ 552 ≤ s.sp.toNat ∧ s.sp.toNat + 40 ≤ 2 ^ 48 ∧ s.mem.accessible (s.sp.toNat - 552) 592 true = true ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 552 ∨ s.sp.toNat + 40 ≤ (s.regs 28).toNat + 16) ∧
        (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
        (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
        (s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧
        (s.regs 3).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 3).toNat 32 false = true ∧
        ((s.regs 0).toNat + 32 ≤ s.sp.toNat - 552 ∨ s.sp.toNat + 40 ≤ (s.regs 0).toNat) ∧
        ((s.regs 1).toNat + 32 ≤ s.sp.toNat - 552 ∨ s.sp.toNat + 40 ≤ (s.regs 1).toNat) ∧
        ((s.regs 2).toNat + 32 ≤ s.sp.toNat - 552 ∨ s.sp.toNat + 40 ≤ (s.regs 2).toNat) ∧
        ((s.regs 3).toNat + 32 ≤ s.sp.toNat - 552 ∨ s.sp.toNat + 40 ≤ (s.regs 3).toNat))
    (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        (s'.regs 1).toNat = (if Fv256.F.muldivOv (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32)
          (s.mem.readLE (s.regs 3).toNat 32) then 1 else 0) ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.muldivSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32)
          (s.mem.readLE (s.regs 3).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 552, s.sp.toNat + 40)]) := by
  intro s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hgw, hzb, hza, hxb, hxa, hyb, hya, hdb, hda, hdz, hdx, hdy, hdd⟩
  have hx0 := Util.readLE8_lt s.mem (s.regs 1).toNat
  have hx1 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 8)
  have hx2 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 16)
  have hx3 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 24)
  have hy0 := Util.readLE8_lt s.mem (s.regs 2).toNat
  have hy1 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 8)
  have hy2 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 16)
  have hy3 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 24)
  have hd0 := Util.readLE8_lt s.mem (s.regs 3).toNat
  have hd1 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 8)
  have hd2 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 16)
  have hd3 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 24)
  janus_run [Nat.or_eq_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div, Util.readLE_32, Fv256.F.wv_zero8, Fv256.F.sum4_eq_zero, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.F.wv_zero4, Fv256.F.wv_zero4', Fv256.B.wv4_eq, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.borrow_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff] calls [Janus.Contracts.EqHashModel.Summary.of_codeIn hcUmul Fv256.Arm64.UmulSum.umul_summary, Janus.Contracts.EqHashModel.Summary.of_codeIn hcChain (Fv256.Arm64.UdivremFinal.udivrem_nil_L_final (L := 8) (by decide) (by decide))]
  · refine ⟨?_, ?_, ?_⟩
    · simp [Fv256.F.muldivOv]
    · simp [Fv256.F.muldivSpec]
    · janus_frame
  · refine ⟨?_, ?_, ?_⟩
    · simp [Fv256.F.muldivOv]
    · simp [Fv256.F.muldivSpec]
    · janus_frame
  · refine ⟨?_, ?_, ?_⟩
    · simp [Fv256.F.muldivOv]
    · simp [Fv256.F.muldivSpec]
    · janus_frame
  · rename_i hmulv hmfU _ _ _ _ _ _ _ hregs hq hfr _
    have hX : (s.mem.readLE (s.regs 1).toNat 8 + 18446744073709551616 * s.mem.readLE ((s.regs 1).toNat + 8) 8 +
        340282366920938463463374607431768211456 * s.mem.readLE ((s.regs 1).toNat + 16) 8 +
        6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE ((s.regs 1).toNat + 24) 8) < 2 ^ 256 := by
      simp only [Nat.reducePow]; omega
    have hY : (s.mem.readLE (s.regs 2).toNat 8 + 18446744073709551616 * s.mem.readLE ((s.regs 2).toNat + 8) 8 +
        340282366920938463463374607431768211456 * s.mem.readLE ((s.regs 2).toNat + 16) 8 +
        6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE ((s.regs 2).toNat + 24) 8) < 2 ^ 256 := by
      simp only [Nat.reducePow]; omega
    have hD0 : (s.mem.readLE (s.regs 3).toNat 8 + 18446744073709551616 * s.mem.readLE ((s.regs 3).toNat + 8) 8 +
        340282366920938463463374607431768211456 * s.mem.readLE ((s.regs 3).toNat + 16) 8 +
        6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE ((s.regs 3).toNat + 24) 8) ≠ 0 := by
      omega
    have key := Fv256.F.mdo_main _ _ _ s.sp.toNat s'.mem (by omega) hD0 hX hY (by rw [hq, hmulv])
    refine ⟨Fv256.F.flag64 _ _ ⟨fun ⟨⟨⟨a, b⟩, c⟩, d⟩ => ⟨d, c, a, b⟩, fun ⟨d, c, a, b⟩ => ⟨⟨⟨a, b⟩, c⟩, d⟩⟩ _ key.1, key.2, ?_⟩
    janus_frame

theorem correctness (z x y d : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, d]
      (fun s => GuardOK s 512 ∧ s.sp.toNat % 16 = 0 ∧ 552 ≤ s.sp.toNat ∧ s.sp.toNat + 40 ≤ 2 ^ 48 ∧
        s.mem.accessible (s.sp.toNat - 552) 592 true = true ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 552 ∨ s.sp.toNat + 40 ≤ (s.regs 28).toNat + 16) ∧
        Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Ptr32 s.mem d false ∧
        Disjoint z.toNat 32 (s.sp.toNat - 552) 592 ∧ Disjoint x.toNat 32 (s.sp.toNat - 552) 592 ∧
        Disjoint y.toNat 32 (s.sp.toNat - 552) 592 ∧ Disjoint d.toNat 32 (s.sp.toNat - 552) 592)
      (fun s s' => s'.regs 0 = z ∧
        (s'.regs 1).toNat = (if Fv256.F.muldivOv (val256 s.mem x.toNat) (val256 s.mem y.toNat) (val256 s.mem d.toNat) then 1 else 0) ∧
        val256 s'.mem z.toNat = Fv256.F.muldivSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) (val256 s.mem d.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 552, s.sp.toNat + 40)]) := by
  refine Fv256.Arm64.SummaryEnsures.ensures_of_summary _ _ mdo_summary ?_ ?_
  · intro ret hret s hsu ⟨hg, hsal, hsb, hsc, hsw, hgw, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, ⟨hd, hd'⟩, hdz, hdx, hdy, hdd⟩
    have h30 : s.regs 30 = BitVec.ofNat 64 ret := by
      have := hsu.lr; exact this
    have h0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have h1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    have h2 : s.regs 2 = y := by have := hsu.args 2 (by simp); simpa using this
    have h3 : s.regs 3 = d := by have := hsu.args 3 (by simp); simpa using this
    rw [h30, h0, h1, h2, h3]
    have ha := hret.aligned
    have hu := hret.user
    refine ⟨?_, ?_, hg, hsal, hsb, hsc, hsw, hgw, hz', hz, hx', hx, hy', hy, hd', hd, ?_, ?_, ?_, ?_⟩
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [Disjoint] at hdz; omega
    · simp only [Disjoint] at hdx; omega
    · simp only [Disjoint] at hdy; omega
    · simp only [Disjoint] at hdd; omega
  · intro ret hret s hsu ⟨hg, hsal, hsb, hsc, hsw, hgw, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, ⟨hd, hd'⟩, hdz, hdx, hdy, hdd⟩ s' ⟨hpc, hsp, h0, h18, h28, h29, h30, hflag, hv, hf⟩
    have e0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have e1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    have e2 : s.regs 2 = y := by have := hsu.args 2 (by simp); simpa using this
    have e3 : s.regs 3 = d := by have := hsu.args 3 (by simp); simpa using this
    rw [e0, e1, e2, e3] at hv
    rw [e1, e2, e3] at hflag
    rw [e0] at hf h0
    refine ⟨⟨hsp, h28, h29, h18⟩, ?_, ?_, ?_, hf⟩
    · exact h0
    · exact hflag
    · exact hv

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

set_option maxRecDepth 200000 in
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then x else if i = 2 then x else if i = 3 then x
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, x, x] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : GuardOK s0 512 ∧ s0.sp.toNat % 16 = 0 ∧ 552 ≤ s0.sp.toNat ∧ s0.sp.toNat + 40 ≤ 2 ^ 48 ∧
        s0.mem.accessible (s0.sp.toNat - 552) 592 true = true ∧
        ((s0.regs 28).toNat + 24 ≤ s0.sp.toNat - 552 ∨ s0.sp.toNat + 40 ≤ (s0.regs 28).toNat + 16) ∧
        Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧ Ptr32 s0.mem x false ∧ Ptr32 s0.mem x false ∧
        Disjoint z.toNat 32 (s0.sp.toNat - 552) 592 ∧ Disjoint x.toNat 32 (s0.sp.toNat - 552) 592 ∧
        Disjoint x.toNat 32 (s0.sp.toNat - 552) 592 ∧ Disjoint x.toNat 32 (s0.sp.toNat - 552) 592 := by
  refine ⟨by unfold GuardOK; decide, by decide, by decide, by decide, by decide, by decide,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_, ?_⟩ <;>
    (unfold Disjoint; decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y d : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y, d] s ∧
    (GuardOK s 512 ∧ s.sp.toNat % 16 = 0 ∧ 552 ≤ s.sp.toNat ∧ s.sp.toNat + 40 ≤ 2 ^ 48 ∧
        s.mem.accessible (s.sp.toNat - 552) 592 true = true ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 552 ∨ s.sp.toNat + 40 ≤ (s.regs 28).toNat + 16) ∧
        Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Ptr32 s.mem d false ∧
        Disjoint z.toNat 32 (s.sp.toNat - 552) 592 ∧ Disjoint x.toNat 32 (s.sp.toNat - 552) 592 ∧
        Disjoint y.toNat 32 (s.sp.toNat - 552) 592 ∧ Disjoint d.toNat 32 (s.sp.toNat - 552) 592) :=
  ⟨ret, s0, z, x, x, x, hret, setup, hpre⟩

end Witness

end Fv256.Arm64.MulDivOverflow
