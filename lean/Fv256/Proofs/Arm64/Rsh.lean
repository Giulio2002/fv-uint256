import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).Rsh(x *Int, n uint) *Int` (arm64): `z = x >> n`

**Guarantee.** For all pointers `z` (receiver, `X0`) and `x` (`X1`) and every Go call state such that the 32 bytes at `z` are
writable, those at `x` readable (below `2^48`) and `z`, `x` are equal or disjoint, and for any shift count `n` (`X2`, any 64-bit value; counts of 256 or more give zero), the call returns (no fault, no panic),
obeys the ABI, returns `z` in `X0`, the number at `z` afterwards is `Fv256.Spec.rsh` of the number at `x`, shifted right by `n`, before the call,
and no byte outside `z[0..32)` changes.

**Non-vacuity.** `Wit.nonvacuous`: a concrete call satisfies the precondition; `Wit.returns`: it returns `z` holding the shifted value of `x`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Rsh

theorem correctness_proof (z x n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, n]
      (fun s => Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Aliasing z x)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.rsh (val256 s.mem x.toNat) n.toNat ∧
        OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hx, hx'⟩, hzx⟩
  janus_intro hs
  rcases hzx with rfl | hzx
  · simp only [Disjoint] at *
    janus_run [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod]
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
  · simp only [Disjoint] at *
    janus_run [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod]
    · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); generalize hm : n.toNat = m at *
      obtain rfl : m = 0 := (by omega)
      simp only [Spec.rsh, Nat.pow_zero, Nat.div_one]
    · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); generalize hm : n.toNat = m at *
      by_cases hlt : m - 192 < 64
      · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
        have hq : 192 + t - 192 = t := (by omega)
        simp only [hq, Nat.mod_eq_of_lt ht, ht, ite_true, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]
        simp only [Spec.rsh]
        rw [Nat.mod_eq_of_lt (Util.readLE8_lt s.mem (x.toNat + 24)), Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))]
      · simp only [if_neg hlt]
        simp only [Spec.rsh]
        rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem x.toNat); have := (Util.readLE8_lt s.mem (x.toNat + 8)); have := (Util.readLE8_lt s.mem (x.toNat + 16)); have := (Util.readLE8_lt s.mem (x.toNat + 24)); omega) (by omega)]
        simp
    · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); generalize hm : n.toNat = m at *
      obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 128 + t := ⟨m - 128, (by omega), (by omega)⟩
      have hc : 18446744073709551616 - (128 + t) - 18446744073709551424 = 64 - t := (by omega)
      have hp : (128 + t - 128) % 64 = t := (by omega)
      simp only [hc, hp]
      rw [Util.shr_or_bv _ _ t ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
      simp only [Spec.rsh]
      exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
    · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); generalize hm : n.toNat = m at *
      have ht1 : 1 ≤ m := (by omega)
      have ht : m < 64 := (by omega)
      have hc : (18446744073709551616 - m - 18446744073709551552) % 64 = (64 - m) % 64 := (by omega)
      simp only [hc, Nat.mod_eq_of_lt ht]
      rw [Util.shr_or_nat _ _ m ht1 ht (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem x.toNat), Util.shr_or_nat _ _ m ht1 ht (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shr_or_nat _ _ m ht1 ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
      simp only [Spec.rsh]
      exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
    · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); generalize hm : n.toNat = m at *
      obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 64 + t := ⟨m - 64, (by omega), (by omega)⟩
      have hc : 18446744073709551616 - (64 + t) - 18446744073709551488 = 64 - t := (by omega)
      have hp : (64 + t - 64) % 64 = t := (by omega)
      simp only [hc, hp]
      rw [Util.shr_or_bv _ _ t ht (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shr_or_bv _ _ t ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
      simp only [Spec.rsh]
      exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))

namespace Wit

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)
def n : BitVec 64 := 0#64

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then x else if i = 2 then n
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, n] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

theorem hpre : Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧ Aliasing z x :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, Or.inr (by unfold Disjoint32 Disjoint z x; decide)⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, n] s ∧
    (Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Aliasing z x) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.rsh (val256 s.mem x.toNat) n.toNat ∧
        OnlyWrites s.mem s'.mem z.toNat 32 :=
  ⟨ret, s0, z, x, n, hret, setup, hpre,
    correctness_proof z x n ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ val256 s'.mem z.toNat = 0 := by
  refine (correctness_proof z x n ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  decide

end Wit

end Fv256.Arm64.Rsh
