import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.Arm64.SummaryEnsures
import Fv256.Arm64.ModSum
import Fv256.Arm64.CodeIn
import Fv256.Arm64.ModProg

/-!
# `(*uint256.Int).IMod(x *Int) *Int` (arm64): in place, `z = z % x`, and `0` when `x = 0`

**Documented behaviour.** `IMod` is `z.Mod(z, x)`: "IMod sets z to the modulus z%x, modifying z in place, and returns z"; `Mod` sets z to the modulus x%y for y != 0 and returns z; if y == 0, z is set to 0.

**Guarantee.** For all pointers `z` (receiver, `X0`) and `x` (`X1`) (they may overlap arbitrarily: `Mod` reads every input limb
before it writes `z`), with the 32 bytes at `z` writable, those at `x` readable (all below `2^48`), neither overlapping the
callee window `[SP-536, SP-32)` (the frame of `IMod` and of the `Mod` it calls), that window writable, and the stack-growth checks
of both falling through (`GuardOK s 496`): the call returns (no fault, no panic), obeys the ABI, returns `z` in `X0`, the number at
`z` afterwards is `Fv256.B.modSpec` of the numbers at `z` and `x` before the call, and nothing changes outside `z[0..32)` and the
window. The callee is used through the verified Extracted-free summary `Fv256.Arm64.ModSum.mod_summary`.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.IMod

set_option maxRecDepth 200000 in
theorem hcMod : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ModProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem imod_summary : Summary Extracted.program Extracted.entry
    (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 496 ∧
        s.sp.toNat % 16 = 0 ∧ 536 ≤ s.sp.toNat ∧ s.sp.toNat ≤ 2 ^ 48 ∧ s.mem.accessible (s.sp.toNat - 536) 504 true = true ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 536 ∨ s.sp.toNat - 32 ≤ (s.regs 28).toNat + 16) ∧
        (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
        (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
        ((s.regs 0).toNat + 32 ≤ s.sp.toNat - 536 ∨ s.sp.toNat - 32 ≤ (s.regs 0).toNat) ∧
        ((s.regs 1).toNat + 32 ≤ s.sp.toNat - 536 ∨ s.sp.toNat - 32 ≤ (s.regs 1).toNat))
    (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 27] → s'.regs i = s.regs i) ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.B.modSpec (s.mem.readLE (s.regs 0).toNat 32) (s.mem.readLE (s.regs 1).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 536, s.sp.toNat - 32)]) := by
  intro s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hgw, hzb, hza, hxb, hxa, hdz, hdx⟩
  janus_run calls [Janus.Contracts.EqHashModel.Summary.of_codeIn hcMod Fv256.Arm64.ModSum.mod_summary]
  rename_i hregs hval hfr _
  refine ⟨?_, hval, ?_⟩
  · intro i hi
    have h := hregs i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    by_cases h30 : i = 30
    · subst h30; simp
    · by_cases h29 : i = 29
      · subst h29; simp
      · rw [if_neg h30, if_neg h29, h]
        repeat' rw [if_neg (by omega)]
  · have hM0 : MemFrame s.mem ((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 (BitVec.toNat (s.regs 30))).writeLE
        (BitVec.toNat s.sp - 56) 8 (BitVec.toNat (s.regs 29)))
        [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 536, s.sp.toNat - 32)] :=
      ((MemFrame.refl s.mem _).writeLE _ (r := (s.sp.toNat - 536, s.sp.toNat - 32)) (by simp) (by dsimp only; omega)
        (by dsimp only; omega)).writeLE _ (r := (s.sp.toNat - 536, s.sp.toNat - 32)) (by simp) (by dsimp only; omega)
        (by dsimp only; omega)
    exact hM0.trans hfr (fun x n hx => by simp only [Outside, and_true] at hx ⊢; omega)

theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x]
      (fun s => GuardOK s 496 ∧ s.sp.toNat % 16 = 0 ∧ 536 ≤ s.sp.toNat ∧ s.sp.toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (s.sp.toNat - 536) 504 true = true ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 536 ∨ s.sp.toNat - 32 ≤ (s.regs 28).toNat + 16) ∧
        Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧
        Disjoint z.toNat 32 (s.sp.toNat - 536) 504 ∧ Disjoint x.toNat 32 (s.sp.toNat - 536) 504)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Fv256.B.modSpec (val256 s.mem z.toNat) (val256 s.mem x.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 536, s.sp.toNat - 32)]) := by
  refine Fv256.Arm64.SummaryEnsures.ensures_of_summary _ _ imod_summary ?_ ?_
  · intro ret hret s hsu ⟨hg, hsal, hsb, hsc, hsw, hgw, ⟨hz, hz'⟩, ⟨hx, hx'⟩, hdz, hdx⟩
    have h30 : s.regs 30 = BitVec.ofNat 64 ret := by
      have := hsu.lr; exact this
    have h0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have h1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    rw [h30, h0, h1]
    have ha := hret.aligned
    have hu := hret.user
    refine ⟨?_, ?_, hg, hsal, hsb, hsc, hsw, hgw, hz', hz, hx', hx, ?_, ?_⟩
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [Disjoint] at hdz; omega
    · simp only [Disjoint] at hdx; omega
  · intro ret hret s hsu ⟨hg, hsal, hsb, hsc, hsw, hgw, ⟨hz, hz'⟩, ⟨hx, hx'⟩, hdz, hdx⟩ s' ⟨hpc, hsp, h0, h18, h28, h29, h30, hr, hv, hf⟩
    have e0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have e1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    rw [e0, e1] at hv
    rw [e0] at hf h0
    refine ⟨⟨hsp, h28, h29, h18⟩, ?_, ?_, hf⟩
    · exact h0
    · exact hv

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

set_option maxRecDepth 200000 in
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then x
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : GuardOK s0 496 ∧ s0.sp.toNat % 16 = 0 ∧ 536 ≤ s0.sp.toNat ∧ s0.sp.toNat ≤ 2 ^ 48 ∧
    s0.mem.accessible (s0.sp.toNat - 536) 504 true = true ∧
    ((s0.regs 28).toNat + 24 ≤ s0.sp.toNat - 536 ∨ s0.sp.toNat - 32 ≤ (s0.regs 28).toNat + 16) ∧
    Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧
    Disjoint z.toNat 32 (s0.sp.toNat - 536) 504 ∧ Disjoint x.toNat 32 (s0.sp.toNat - 536) 504 := by
  refine ⟨by unfold GuardOK; decide, by decide, by decide, by decide, by decide, by decide,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_⟩ <;>
    (unfold Disjoint; decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧
    (GuardOK s 496 ∧ s.sp.toNat % 16 = 0 ∧ 536 ≤ s.sp.toNat ∧ s.sp.toNat ≤ 2 ^ 48 ∧
      s.mem.accessible (s.sp.toNat - 536) 504 true = true ∧
      ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 536 ∨ s.sp.toNat - 32 ≤ (s.regs 28).toNat + 16) ∧
      Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧
      Disjoint z.toNat 32 (s.sp.toNat - 536) 504 ∧ Disjoint x.toNat 32 (s.sp.toNat - 536) 504) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Fv256.B.modSpec (val256 s.mem z.toNat) (val256 s.mem x.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 536, s.sp.toNat - 32)] :=
  ⟨ret, s0, z, x, hret, setup, hpre,
    correctness z x ret hret s0 setup hpre⟩

end Witness

end Fv256.Arm64.IMod
