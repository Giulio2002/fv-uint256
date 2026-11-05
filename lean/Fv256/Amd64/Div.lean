import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.CodeIn
import Fv256.Amd64.UdivremA
import Fv256.Amd64.UdivremK
import Fv256.Amd64.UdivremL

/-!
# `(*uint256.Int).Div(x, y *Int) *Int` (amd64): `z = x / y`, and `0` when `y = 0`

**Guarantee.** For all pointers `z` (receiver, `RAX`), `x` (`RBX`), `y` (`RCX`) (the three may overlap arbitrarily: every
input limb is read before `z` is written, and the quotient is computed in a local `Int`), and every Go call in which the
stack-growth checks of `Div` and of the callee `udivrem` fall through (`StackGuardOK s 0x168`), the window
`[RSP-0x1b8, RSP+0x10)` (the frames of `Div` and `udivrem` and the caller's spill slot of `z`) is writable, the 32 bytes
at `z` are writable, those at `x` and `y` readable (all below `2^48`), none of them overlaps the window, and the goroutine's
`stackguard0` word is outside the window, the call returns (no fault, no panic, no `#DE`), obeys the ABI (including
`X15 = 0`, `R14`, `RBP`), returns `z` in `RAX`, the number at `z` afterwards is `Fv256.B.divSpec` of the numbers at `x` and `y`
before the call (`x / y`, or `0` when `y = 0`), and no byte outside `z[0..32)` and the window changes
(`MemFrame`: bytes outside the two ranges are unchanged and the accessibility of every region is unchanged).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z` with value `0`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Div

set_option maxRecDepth 100000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ChainProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => StackGuardOK s 0x168 ∧ 0x1c0 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x1b8 0x10 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x1b8 ∨ (s.regs regSP).toNat + 0x10 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x1b8 ∨ (s.regs regSP).toNat + 0x10 ≤ x.toNat) ∧
        (y.toNat + 32 ≤ (s.regs regSP).toNat - 0x1b8 ∨ (s.regs regSP).toNat + 0x10 ≤ y.toNat) ∧
        ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x1b8 ∨ (s.regs regSP).toNat + 0x10 ≤ (s.regs regG).toNat + 16))
      (fun s s' => s'.regs 0 = z ∧ valueAt s' z 32 = Fv256.B.divSpec (valueAt s x 32) (valueAt s y 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x1b8, (s.regs regSP).toNat + 0x10)]) := by
  intro ret hret s hs ⟨hg, hsp, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, hdz, hdx, hdy, hdg⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hdx hdy hsp hsp
  simp only [valueAt]
  have hx0 := Util.readLE8_lt s.mem x.toNat
  have hx1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have hx2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have hx3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hy0 := Util.readLE8_lt s.mem y.toNat
  have hy1 := Util.readLE8_lt s.mem (y.toNat + 8)
  have hy2 := Util.readLE8_lt s.mem (y.toNat + 16)
  have hy3 := Util.readLE8_lt s.mem (y.toNat + 24)
  have hdv := Nat.div_le_self (s.mem.readLE x.toNat 8) (s.mem.readLE y.toNat 8)
  janus64_run [Util.readLE_32, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.B.wv4_eq, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.borrow_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div] calls [Fv256.CodeIn.lib_summary hcChain Fv256.Amd64.UdivremL.udivrem_nil]
  all_goals (first | (exfalso; omega) | skip)
  all_goals (refine ⟨?_, ?_⟩)
  all_goals (first | janus_frame | skip)
  all_goals (first
    | (have e8 : BitVec.toNat (s.regs 4) - 32 = BitVec.toNat (s.regs 4) - 40 + 8 := by omega
       have e16 : BitVec.toNat (s.regs 4) - 24 = BitVec.toNat (s.regs 4) - 40 + 16 := by omega
       have e24 : BitVec.toNat (s.regs 4) - 16 = BitVec.toNat (s.regs 4) - 40 + 24 := by omega
       rw [e8, e16, e24])
    | skip)
  all_goals (first
    | (exfalso; omega)
    | (rw [Fv256.B.divSpec]
       split <;>
         (first
           | omega
           | (exfalso; omega)
           | exact Fv256.B.one_eq_div _ _ (by omega) (by omega)
           | exact (Nat.div_eq_of_lt (by omega)).symm
           | exact Fv256.B.div_congr _ _ _ (by omega)))
    | skip)

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

theorem hpre : StackGuardOK s0 0x168 ∧ 0x1c0 ≤ (s0.regs regSP).toNat ∧ StackWritable s0 0x1b8 0x10 ∧ Buffer s0 z 32 true ∧
    Buffer s0 x 32 false ∧ Buffer s0 x 32 false ∧
    (z.toNat + 32 ≤ (s0.regs regSP).toNat - 0x1b8 ∨ (s0.regs regSP).toNat + 0x10 ≤ z.toNat) ∧
    (x.toNat + 32 ≤ (s0.regs regSP).toNat - 0x1b8 ∨ (s0.regs regSP).toNat + 0x10 ≤ x.toNat) ∧
    (x.toNat + 32 ≤ (s0.regs regSP).toNat - 0x1b8 ∨ (s0.regs regSP).toNat + 0x10 ≤ x.toNat) ∧
    ((s0.regs regG).toNat + 24 ≤ (s0.regs regSP).toNat - 0x1b8 ∨ (s0.regs regSP).toNat + 0x10 ≤ (s0.regs regG).toNat + 16) :=
  ⟨⟨by decide, by decide, by decide⟩, by unfold regSP; decide, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by unfold regSP; decide, by unfold regSP; decide, by unfold regSP; decide,
    by unfold regSP regG; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧
    (StackGuardOK s 0x168 ∧ 0x1c0 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x1b8 0x10 ∧ Buffer s z 32 true ∧
      Buffer s x 32 false ∧ Buffer s y 32 false ∧
      (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x1b8 ∨ (s.regs regSP).toNat + 0x10 ≤ z.toNat) ∧
      (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x1b8 ∨ (s.regs regSP).toNat + 0x10 ≤ x.toNat) ∧
      (y.toNat + 32 ≤ (s.regs regSP).toNat - 0x1b8 ∨ (s.regs regSP).toNat + 0x10 ≤ y.toNat) ∧
      ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x1b8 ∨ (s.regs regSP).toNat + 0x10 ≤ (s.regs regG).toNat + 16)) :=
  ⟨ret, s0, z, x, x, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ valueAt s' z 32 = 0 := by
  refine (correctness z x x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  simp only [valueAt, Fv256.B.divSpec]
  decide

end Witness

end Fv256.Amd64.Div
