import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.SpecB2
import Fv256.Proofs.Common.UtilB2
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Common.UtilF
import Fv256.Proofs.Arm64.SummaryEnsures
import Fv256.Proofs.Arm64.CodeIn
import Fv256.Proofs.Arm64.UmulProg
import Fv256.Proofs.Arm64.UmulSum
import Fv256.Proofs.Arm64.ChainProg
import Fv256.Proofs.Arm64.UdivremFinal
import Fv256.Proofs.Arm64.MdorLemmas
import Fv256.Proofs.Arm64.DivLemmas

/-!
# `(*uint256.Int).MulDivOverflowRem(x, y, d, m *Int) (*Int, *Int, bool)` (arm64)

**Documented behaviour.** `z.MulDivOverflowRem(x, y, d, m)` sets `z` to the low 256 bits of the quotient `x*y/d` (the product is
computed in full, 512 bits), `m` to the remainder `x*y mod d`, and returns `(z, m, overflow)` with `overflow` set when the quotient
does not fit in 256 bits.  If `x`, `y` or `d` is zero, `z` and `m` are cleared and the result is `(z, m, false)`.

**Guarantee.** For pointers `z`, `x`, `y`, `d`, `m` (`X0`..`X4`), `z`, `m` writable and the others readable (below `2^48`), `z`, `x`, `y`, `d`
apart from the stack window and from `m` (`z`, `x`, `y`, `d` may alias each other: every input limb is read before `z` is written), the
call returns, obeys the ABI, returns `z`, `m` and the flag, the numbers at `z` and `m` are `Fv256.F.muldivSpec` and `Fv256.F.mulmodSpec`
of the inputs, the flag is `Fv256.F.muldivOv`, and nothing changes outside `z[0..32)`, `m[0..32)` and the frame window.
Callees are used through the verified Extracted-free summaries `Fv256.Arm64.UmulSum.umul_summary` and
`Fv256.Arm64.UdivremFinal.udivrem_rem_L_final`.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.MulDivOverflowRem

set_option maxRecDepth 200000 in
theorem hcUmul : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.UmulProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 200000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ChainProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem mdor_summary : Summary Extracted.program Extracted.entry
    (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 512 ∧ StackOK s 552 48 ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 552) 600 ∧
        (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
        (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
        (s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧
        (s.regs 3).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 3).toNat 32 false = true ∧
        (s.regs 4).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 4).toNat 32 true = true ∧
        Apart (s.regs 0).toNat 32 (s.sp.toNat - 552) 600 ∧ Apart (s.regs 1).toNat 32 (s.sp.toNat - 552) 600 ∧
        Apart (s.regs 2).toNat 32 (s.sp.toNat - 552) 600 ∧ Apart (s.regs 3).toNat 32 (s.sp.toNat - 552) 600 ∧
        Apart (s.regs 4).toNat 32 (s.sp.toNat - 552) 600 ∧
        Apart (s.regs 0).toNat 32 (s.regs 4).toNat 32 ∧ Apart (s.regs 1).toNat 32 (s.regs 4).toNat 32 ∧
        Apart (s.regs 2).toNat 32 (s.regs 4).toNat 32 ∧ Apart (s.regs 3).toNat 32 (s.regs 4).toNat 32 ∧
        Apart (s.regs 4).toNat 32 ((s.regs 28).toNat + 16) 8 ∧ (s.regs 4).toNat ≠ 0)
    (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 1 = s.regs 4 ∧
        s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        (s'.regs 2).toNat = (if Fv256.F.muldivOv (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32)
          (s.mem.readLE (s.regs 3).toNat 32) then 1 else 0) ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.muldivSpec (s.mem.readLE (s.regs 1).toNat 32)
          (s.mem.readLE (s.regs 2).toNat 32) (s.mem.readLE (s.regs 3).toNat 32) ∧
        s'.mem.readLE (s.regs 4).toNat 32 = Fv256.F.mulmodSpec (s.mem.readLE (s.regs 1).toNat 32)
          (s.mem.readLE (s.regs 2).toNat 32) (s.mem.readLE (s.regs 3).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat, (s.regs 4).toNat + 32),
          (s.sp.toNat - 552, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 48)]) := by
  intro s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, ⟨hsal, hsb, hsc, hsw⟩, hgs, hzb, hza, hxb, hxa, hyb, hya, hdb, hda, hmb, hma,
    hdz, hdx, hdy, hdd, hdm, hzm, hxm, hym, hdmm, hmg, hm0⟩
  janus_run [Util.readLE_32, Nat.or_eq_zero_iff, Fv256.B.wv4_eq, Fv256.B.wv_writeLE_outside, Fv256.Arm64.MdorLemmas.wv_zero8w, Fv256.Arm64.DivLemmas.wv_zero4w, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div] calls [Janus.Contracts.EqHashModel.Summary.of_codeIn hcUmul Fv256.Arm64.UmulSum.umul_summary,
    Janus.Contracts.EqHashModel.Summary.of_codeIn hcLib (Fv256.Arm64.UdivremFinal.udivrem_rem_L_final (L := 8) (by decide) (by decide))]
  all_goals (first
    | (refine ⟨?_, ?_, ?_, ?_⟩
       · simp_all [Fv256.F.muldivOv, Fv256.F.muldivSpec, Fv256.F.mulmodSpec]
       · simp_all [Fv256.F.muldivOv, Fv256.F.muldivSpec, Fv256.F.mulmodSpec]
       · simp_all [Fv256.F.muldivOv, Fv256.F.muldivSpec, Fv256.F.mulmodSpec]
       · janus_frame)
    | skip)
  have x0 := Util.readLE8_lt s.mem (s.regs 1).toNat
  have x1 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 8)
  have x2 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 16)
  have x3 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 24)
  have y0 := Util.readLE8_lt s.mem (s.regs 2).toNat
  have y1 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 8)
  have y2 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 16)
  have y3 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 24)
  have d0 := Util.readLE8_lt s.mem (s.regs 3).toNat
  have d1 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 8)
  have d2 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 16)
  have d3 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 24)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Fv256.Arm64.MdorLemmas.tail_flag _ _ s.sp.toNat _ _ _ (by omega) (by omega) (by omega) (by omega)
      (by janus_assumption) (by janus_assumption)
  · exact Fv256.Arm64.MdorLemmas.tail_z _ _ s.sp.toNat _ _ _ (by omega) (by omega) (by omega) (by omega)
      (by janus_assumption) (by janus_assumption)
  · exact Fv256.Arm64.MdorLemmas.tail_m _ s.sp.toNat _ _ _ _ (by omega) (by janus_assumption) (by janus_assumption)
  · janus_frame

theorem correctness (z x y d m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, d, m]
      (fun s => GuardOK s 512 ∧ s.sp.toNat % 16 = 0 ∧ 552 ≤ s.sp.toNat ∧ s.sp.toNat + 48 ≤ 2 ^ 48 ∧
        s.mem.accessible (s.sp.toNat - 552) (552 + 48) true = true ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 552) 600 ∧
        Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Ptr32 s.mem d false ∧ Ptr32 s.mem m true ∧
        Apart z.toNat 32 (s.sp.toNat - 552) 600 ∧ Apart x.toNat 32 (s.sp.toNat - 552) 600 ∧
        Apart y.toNat 32 (s.sp.toNat - 552) 600 ∧ Apart d.toNat 32 (s.sp.toNat - 552) 600 ∧
        Apart m.toNat 32 (s.sp.toNat - 552) 600 ∧
        Apart z.toNat 32 m.toNat 32 ∧ Apart x.toNat 32 m.toNat 32 ∧ Apart y.toNat 32 m.toNat 32 ∧
        Apart d.toNat 32 m.toNat 32 ∧ Apart m.toNat 32 ((s.regs 28).toNat + 16) 8 ∧ m.toNat ≠ 0)
      (fun s s' => s'.regs 0 = z ∧ s'.regs 1 = m ∧
        (s'.regs 2).toNat = (if Fv256.F.muldivOv (val256 s.mem x.toNat) (val256 s.mem y.toNat) (val256 s.mem d.toNat)
          then 1 else 0) ∧
        val256 s'.mem z.toNat = Fv256.F.muldivSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) (val256 s.mem d.toNat) ∧
        val256 s'.mem m.toNat = Fv256.F.mulmodSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) (val256 s.mem d.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (m.toNat, m.toNat + 32), (s.sp.toNat - 552, s.sp.toNat - 8),
          (s.sp.toNat + 8, s.sp.toNat + 48)]) := by
  refine Fv256.Arm64.SummaryEnsures.ensures_of_summary _ _ mdor_summary ?_ ?_
  · intro ret hret s hsu ⟨hg, hsal, hsb, hsc, hsw, hgs, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, ⟨hd, hd'⟩, ⟨hm, hm'⟩,
      hdz, hdx, hdy, hdd, hdm, hzm, hxm, hym, hdmm, hmg, hm0⟩
    have h30 : s.regs 30 = BitVec.ofNat 64 ret := by
      have := hsu.lr; exact this
    have h0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have h1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    have h2 : s.regs 2 = y := by have := hsu.args 2 (by simp); simpa using this
    have h3 : s.regs 3 = d := by have := hsu.args 3 (by simp); simpa using this
    have h4 : s.regs 4 = m := by have := hsu.args 4 (by simp); simpa using this
    rw [h30, h0, h1, h2, h3, h4]
    have ha := hret.aligned
    have hu := hret.user
    refine ⟨?_, ?_, hg, ⟨hsal, hsb, hsc, hsw⟩, hgs, hz', hz, hx', hx, hy', hy, hd', hd, hm', hm,
      hdz, hdx, hdy, hdd, hdm, hzm, hxm, hym, hdmm, hmg, hm0⟩
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
  · intro ret hret s hsu ⟨hg, hsal, hsb, hsc, hsw, hgs, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, ⟨hd, hd'⟩, ⟨hm, hm'⟩,
      hdz, hdx, hdy, hdd, hdm, hzm, hxm, hym, hdmm, hmg, hm0⟩ s' ⟨hpc, hsp, h0', h1', h18, h28, h29, h30, hfl, hv, hmv, hf⟩
    have e0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have e1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    have e2 : s.regs 2 = y := by have := hsu.args 2 (by simp); simpa using this
    have e3 : s.regs 3 = d := by have := hsu.args 3 (by simp); simpa using this
    have e4 : s.regs 4 = m := by have := hsu.args 4 (by simp); simpa using this
    simp only [e0, e1, e2, e3, e4] at h0' h1' hfl hv hmv hf
    refine ⟨⟨hsp, h28, h29, h18⟩, h0', h1', ?_, ?_, ?_, hf⟩
    · simp only [val256]
      split at hfl <;> simp_all
    · simpa only [val256] using hv
    · simpa only [val256] using hmv

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

set_option maxRecDepth 200000 in
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)
def m : BitVec 64 := BitVec.ofNat 64 (DST + 0x80)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then x else if i = 2 then x else if i = 3 then x else if i = 4 then m
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, x, x, m] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : GuardOK s0 512 ∧ s0.sp.toNat % 16 = 0 ∧ 552 ≤ s0.sp.toNat ∧ s0.sp.toNat + 48 ≤ 2 ^ 48 ∧
        s0.mem.accessible (s0.sp.toNat - 552) (552 + 48) true = true ∧
        Apart ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 552) 600 ∧
        Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧ Ptr32 s0.mem x false ∧ Ptr32 s0.mem x false ∧ Ptr32 s0.mem m true ∧
        Apart z.toNat 32 (s0.sp.toNat - 552) 600 ∧ Apart x.toNat 32 (s0.sp.toNat - 552) 600 ∧
        Apart x.toNat 32 (s0.sp.toNat - 552) 600 ∧ Apart x.toNat 32 (s0.sp.toNat - 552) 600 ∧
        Apart m.toNat 32 (s0.sp.toNat - 552) 600 ∧
        Apart z.toNat 32 m.toNat 32 ∧ Apart x.toNat 32 m.toNat 32 ∧ Apart x.toNat 32 m.toNat 32 ∧
        Apart x.toNat 32 m.toNat 32 ∧ Apart m.toNat 32 ((s0.regs 28).toNat + 16) 8 ∧ m.toNat ≠ 0 := by
  refine ⟨by unfold GuardOK; decide, by decide, by decide, by decide, by decide, ?_,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide⟩ <;>
    (unfold Apart; decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y d m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y, d, m] s ∧
    (GuardOK s 512 ∧ s.sp.toNat % 16 = 0 ∧ 552 ≤ s.sp.toNat ∧ s.sp.toNat + 48 ≤ 2 ^ 48 ∧
        s.mem.accessible (s.sp.toNat - 552) (552 + 48) true = true ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 552) 600 ∧
        Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Ptr32 s.mem d false ∧ Ptr32 s.mem m true ∧
        Apart z.toNat 32 (s.sp.toNat - 552) 600 ∧ Apart x.toNat 32 (s.sp.toNat - 552) 600 ∧
        Apart y.toNat 32 (s.sp.toNat - 552) 600 ∧ Apart d.toNat 32 (s.sp.toNat - 552) 600 ∧
        Apart m.toNat 32 (s.sp.toNat - 552) 600 ∧
        Apart z.toNat 32 m.toNat 32 ∧ Apart x.toNat 32 m.toNat 32 ∧ Apart y.toNat 32 m.toNat 32 ∧
        Apart d.toNat 32 m.toNat 32 ∧ Apart m.toNat 32 ((s.regs 28).toNat + 16) 8 ∧ m.toNat ≠ 0) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧ s'.regs 1 = m ∧
        (s'.regs 2).toNat = (if Fv256.F.muldivOv (val256 s.mem x.toNat) (val256 s.mem y.toNat) (val256 s.mem d.toNat)
          then 1 else 0) ∧
        val256 s'.mem z.toNat = Fv256.F.muldivSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) (val256 s.mem d.toNat) ∧
        val256 s'.mem m.toNat = Fv256.F.mulmodSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) (val256 s.mem d.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (m.toNat, m.toNat + 32), (s.sp.toNat - 552, s.sp.toNat - 8),
          (s.sp.toNat + 8, s.sp.toNat + 48)] :=
  ⟨ret, s0, z, x, x, x, m, hret, setup, hpre,
    correctness z x x x m ret hret s0 setup hpre⟩

end Witness

end Fv256.Arm64.MulDivOverflowRem
