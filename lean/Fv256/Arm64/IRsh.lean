import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).IRsh(n uint) *Int` (arm64): in place, `z = z >> n`

**Guarantee.** For every pointer `z` (receiver, `X0`), every shift count `n` (`X1`, any 64-bit value; counts of 256 or more give
zero) and every Go call state such that the stack-growth check falls through (`GuardOK s 0`), the window `[SP-56, SP)` (the 56-byte
frame) is writable and aligned (`StackOK s 56 0`), the 32 bytes at `z` are writable and do not overlap the frame window: the call
returns (no fault, no panic), obeys the ABI, returns `z` in `X0`, the number at `z` afterwards is `Fv256.Spec.rsh` of the number at
`z` before the call, shifted by `n`, and no byte outside `z[0..32)` and the frame window changes (`Fv256.Util.OnlyWrites2`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.IRsh

theorem correctness (z n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, n]
      (fun s => GuardOK s 0 ∧ StackOK s 56 0 ∧ Ptr32 s.mem z true ∧ Disjoint z.toNat 32 (s.sp.toNat - 56) 56)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.rsh (val256 s.mem z.toNat) n.toNat ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 56) 56) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hz, hz'⟩, hd1⟩
  janus_intro hs
  simp only [Disjoint] at *
  janus_run [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod]
  all_goals refine And.intro ?_ (by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff])
  · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); generalize hm : n.toNat = m at *
    obtain rfl : m = 0 := (by omega)
    simp only [Spec.rsh, Nat.pow_zero, Nat.div_one]
  · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); generalize hm : n.toNat = m at *
    by_cases hlt : m - 192 < 64
    · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
      have hq : 192 + t - 192 = t := (by omega)
      simp only [hq, Nat.mod_eq_of_lt ht, ht, ite_true, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]
      simp only [Spec.rsh]
      rw [Nat.mod_eq_of_lt (Util.readLE8_lt s.mem (z.toNat + 24)), Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))]
    · simp only [if_neg hlt]
      simp only [Spec.rsh]
      rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem z.toNat); have := (Util.readLE8_lt s.mem (z.toNat + 8)); have := (Util.readLE8_lt s.mem (z.toNat + 16)); have := (Util.readLE8_lt s.mem (z.toNat + 24)); omega) (by omega)]
      simp
  · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); generalize hm : n.toNat = m at *
    obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 128 + t := ⟨m - 128, (by omega), (by omega)⟩
    have hc : 18446744073709551616 - (128 + t) - 18446744073709551424 = 64 - t := (by omega)
    have hp : (128 + t - 128) % 64 = t := (by omega)
    simp only [hc, hp]
    rw [Util.shr_or_bv _ _ t ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
    simp only [Spec.rsh]
    exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
  · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); generalize hm : n.toNat = m at *
    have ht1 : 1 ≤ m := (by omega)
    have ht : m < 64 := (by omega)
    have hc : (18446744073709551616 - m - 18446744073709551552) % 64 = (64 - m) % 64 := (by omega)
    simp only [hc, Nat.mod_eq_of_lt ht]
    rw [Util.shr_or_nat _ _ m ht1 ht (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem z.toNat), Util.shr_or_nat _ _ m ht1 ht (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shr_or_nat _ _ m ht1 ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
    simp only [Spec.rsh]
    exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
  · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); generalize hm : n.toNat = m at *
    obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 64 + t := ⟨m - 64, (by omega), (by omega)⟩
    have hc : 18446744073709551616 - (64 + t) - 18446744073709551488 = 64 - t := (by omega)
    have hp : (64 + t - 64) % 64 = t := (by omega)
    simp only [hc, hp]
    rw [Util.shr_or_bv _ _ t ht (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shr_or_bv _ _ t ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
    simp only [Spec.rsh]
    exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def n : BitVec 64 := 0#64

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then n
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hpre : GuardOK s0 0 ∧ StackOK s0 56 0 ∧ Ptr32 s0.mem z true ∧ Disjoint z.toNat 32 (s0.sp.toNat - 56) 56 :=
  ⟨by unfold GuardOK; decide, by unfold StackOK; decide, ⟨by decide, by decide⟩, by unfold Disjoint; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s ∧
    (GuardOK s 0 ∧ StackOK s 56 0 ∧ Ptr32 s.mem z true ∧ Disjoint z.toNat 32 (s.sp.toNat - 56) 56) :=
  ⟨ret, s0, z, n, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ val256 s'.mem z.toNat = 0 := by
  refine (correctness z n ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  decide

end Witness

end Fv256.Arm64.IRsh
