import Fv256.Proofs.Arm64.RecipG.C_88_108
import Fv256.Proofs.Arm64.RecipBridge
import Fv256.Proofs.Common.UtilAM
import Fv256.Proofs.Arm64.RecipBv

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.RecipSeg
open Fv256.F

theorem sum1 (s S : State) (x88m32 x88m40 x88m48 x88m56 x88m176 : Nat)
    (h : PC_88_108 s x88m32 x88m40 x88m48 x88m56 x88m176 S)
    (b0 : x88m32 < 2 ^ 64) (b1 : x88m40 < 2 ^ 64) (b2 : x88m48 < 2 ^ 64) (hb : x88m56 < 2 ^ 64) (h63 : 2 ^ 63 ≤ x88m56) :
    ∃ x108r0 x108m176, L108 S x108r0 18446744073709551615 x88m48 x88m56 x88m32 x88m40 x108m176 x88m32 x88m40 x88m48 ∧
      x108r0 = recipR1 (x88m32 + 2 ^ 64 * x88m40 + 2 ^ 128 * x88m48 + 2 ^ 192 * x88m56) ∧
      x108m176 = (18446744073709551615 + x88m176 % 64) % 18446744073709551616 ∧ RecRegs s S ∧ RecMem s S.mem := by
  unfold PC_88_108 at h
  obtain ⟨xbcr0, x108r0, x108m176, hL, h_xbcr0, h_x108r0, h_x108m176, hx0, hx1, hR, hM⟩ := h
  refine ⟨x108r0, x108m176, hL, ?_, h_x108m176, hR, hM⟩
  try simp only [Fv256.Arm64.RecipBv.rot32_shl, Fv256.Arm64.RecipBv.rot32_hi, Fv256.Arm64.RecipBv.toNat_ite, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_setWidth, BitVec.toNat_mul, Janus.Tactic.umulh_toNat, Nat.reducePow] at h_x108r0
  obtain ⟨w0, w1, w2, w3⟩ := Fv256.Arm64.RecipBridge.yw_words x88m32 x88m40 x88m48 x88m56 b0 b1 b2 hb
  have hxb : xbcr0 < 2 ^ 64 := by
    rw [h_xbcr0]; split
    · decide
    · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by decide)
  have hr0 : recipR0 (x88m32 + 2 ^ 64 * x88m40 + 2 ^ 128 * x88m48 + 2 ^ 192 * x88m56) = xbcr0 % 2 ^ 32 := by
    rw [hx0]; unfold recipR0 r0f; rw [w3]
  have hsh : xbcr0 * 2 ^ 32 % 2 ^ 64 = xbcr0 % 2 ^ 32 * 2 ^ 32 := by
    have : (2:Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
    rw [this, Nat.mul_comm xbcr0, Nat.mul_mod_mul_left]; exact Nat.mul_comm _ _
  unfold recipR1 recipR1raw recipT1
  rw [hr0, w3]
  rw [h_x108r0]
  simp only [Nat.mod_eq_of_lt hxb, Nat.mod_eq_of_lt hb, Nat.shiftLeft_eq, hsh, Nat.reducePow, Nat.mod_mod, show 4294967296 = 2 ^ 32 from rfl] 
  have hr32 : xbcr0 % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  have hr32 : xbcr0 % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  have hT : xbcr0 % 4294967296 * (xbcr0 % 4294967296) % 18446744073709551616 * x88m56 / 18446744073709551616 < 18446744073709551616 := by
    apply Nat.div_lt_of_lt_mul
    have h1 : xbcr0 % 4294967296 * (xbcr0 % 4294967296) % 18446744073709551616 < 18446744073709551616 := Nat.mod_lt _ (by decide)
    have := Nat.mul_lt_mul'' h1 hb
    simpa [Nat.mul_comm] using this
  generalize xbcr0 % 4294967296 * (xbcr0 % 4294967296) % 18446744073709551616 * x88m56 / 18446744073709551616 = T at *
  generalize hrr : xbcr0 % 4294967296 = r at *
  have key : ∀ X Y : Nat, X % 18446744073709551616 = Y % 18446744073709551616 → (X + X) % 18446744073709551616 = (Y + Y) % 18446744073709551616 := by intro X Y h; omega
  have hA : (18446744073709551616 - T + xbcr0 * 4294967296) % 18446744073709551616 = (18446744073709551616 - T + r * 4294967296) % 18446744073709551616 := by
    have : xbcr0 * 4294967296 = r * 4294967296 + 18446744073709551616 * (xbcr0 / 4294967296) := by omega
    omega
  have e1 : (18446744073709551616 - T + r * 4294967296 + (18446744073709551616 - T + r * 4294967296)) % 18446744073709551616 =
      2 * ((r * 4294967296 + 18446744073709551616 - T) % 18446744073709551616) % 18446744073709551616 := by omega
  rw [key _ _ hA, e1, Nat.mul_comm x88m56 2]

end Fv256.Arm64.RecipSeg
