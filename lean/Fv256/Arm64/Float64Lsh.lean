import Extracted
import Fv256.Spec
import Fv256.Util

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Float64

/-- `Lsh(z, x, n)` as a callee (`z` in `X0`, `x` in `X1`, `n` in `X2`), `z` and `x` disjoint. -/
def LshSummary (p : Program) (entry : Nat) (z x : BitVec 64) : Prop :=
  Summary p entry
    (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ s.regs 0 = z ∧ s.regs 1 = x ∧
      Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Disjoint z.toNat 32 x.toNat 32)
    (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
      s'.regs 30 = s.regs 30 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 0 = z ∧
      val256 s'.mem z.toNat = Spec.lsh (val256 s.mem x.toNat) (s.regs 2).toNat ∧
      MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32)])

set_option maxHeartbeats 16000000 in
theorem lsh_summary (z x : BitVec 64) :
    LshSummary Extracted.program (segAddr Extracted.program "github.com/holiman/uint256.(*Int).Lsh") z x := by
  intro s hpc ⟨h30a, h30b, hz0, hx0, ⟨hz, hz'⟩, ⟨hx, hx'⟩, hd⟩
  simp only [Disjoint] at *
  janus_run [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod]
  all_goals (refine ⟨?_, ?_⟩; rotate_right; janus_frame)
  · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); generalize hm : (s.regs 2).toNat = m at *; obtain rfl : m = 0 := (by omega); simp only [Spec.lsh, Spec.W, Nat.reducePow, Nat.pow_zero, Nat.mul_one]; first | done | rw [Nat.mod_eq_of_lt (by have := (Util.readLE8_lt s.mem x.toNat); have := (Util.readLE8_lt s.mem (x.toNat + 8)); have := (Util.readLE8_lt s.mem (x.toNat + 16)); have := (Util.readLE8_lt s.mem (x.toNat + 24)); omega)]
  · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); generalize hm : (s.regs 2).toNat = m at *; by_cases hlt : m - 192 < 64
    · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
      have hq : 192 + t - 192 = t := (by omega)
      simp only [hq, Nat.mod_eq_of_lt ht, ht, ite_true, BitVec.toNat_ofNat, Nat.reducePow]
      simp only [Spec.lsh, Spec.W, Nat.reducePow]
      exact Util.lsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
    · simp only [if_neg hlt]
      simp only [Spec.lsh, Spec.W, Nat.reducePow]
      rw [Util.lsh_big _ _ (by omega)]
      simp
  · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); generalize hm : (s.regs 2).toNat = m at *; obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 128 + t := ⟨m - 128, by omega, by omega⟩; have hc : 18446744073709551616 - (128 + t) - 18446744073709551424 = 64 - t := (by omega); have hp : (128 + t - 128) % 64 = t := (by omega); simp only [hc, hp]; rw [Util.shl_or_bv _ _ t ht (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem x.toNat)]; simp only [Spec.lsh, Spec.W, Nat.reducePow]; exact Util.lsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
  · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); generalize hm : (s.regs 2).toNat = m at *; have ht1 : 1 ≤ m := (by omega); have ht : m < 64 := (by omega); have hc : (18446744073709551616 - m - 18446744073709551552) % 64 = (64 - m) % 64 := (by omega); simp only [hc, Nat.mod_eq_of_lt ht]; rw [Util.shl_or_bv0 _ _ m ht1 ht (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem x.toNat), Util.shl_or_bv0 _ _ m ht1 ht (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shl_or_bv0 _ _ m ht1 ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]; simp only [Spec.lsh, Spec.W, Nat.reducePow]; exact Util.lsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
  · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); generalize hm : (s.regs 2).toNat = m at *; obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 64 + t := ⟨m - 64, by omega, by omega⟩; have hc : 18446744073709551616 - (64 + t) - 18446744073709551488 = 64 - t := (by omega); have hp : (64 + t - 64) % 64 = t := (by omega); simp only [hc, hp]; rw [Util.shl_or_bv _ _ t ht (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shl_or_bv _ _ t ht (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem x.toNat)]; simp only [Spec.lsh, Spec.W, Nat.reducePow]; exact Util.lsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))

end Fv256.Arm64.Float64
