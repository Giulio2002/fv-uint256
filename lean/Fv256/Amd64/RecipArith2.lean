import Fv256.Amd64.RecipG.C_14c_1f3
import Fv256.Amd64.RecipStart
import Fv256.RecipStages

open Janus Janus.Amd64

namespace Fv256.Amd64.RecipSeg
open Fv256.RecipMath

/-- `r1` after the `cmove`: `2^64 - 1` when `r1raw | 2 y3 = 0`, else `r1raw` -/
def r1c (ax dx : Nat) : Nat := if dx = 0 then 18446744073709551615 else ax

theorem mulb (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) : a * b < 2^128 := by
  have := Nat.mul_lt_mul'' ha hb; simpa [← Nat.pow_add] using this

theorem pos_toNat (z : Nat) (hz : z ≤ 18446744073709551616) : (decide (0 < z)).toNat = 1 - (18446744073709551616 - z) / 18446744073709551616 := by
  rcases Nat.eq_zero_or_pos z with h | h
  · subst h; decide
  · have : (18446744073709551616 - z) / 18446744073709551616 = 0 := Nat.div_eq_of_lt (by omega)
    simp [h, this]

theorem rcx_bv (x : Nat) : (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 x) &&& 63#32) - 1#64).toNat = (x % 64 + 18446744073709551615) % 18446744073709551616 := by
  have h : (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 x) &&& 63#32)).toNat = x % 64 := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
    have h63 : (63 : Nat) = 2 ^ 6 - 1 := by decide
    have : x % 4294967296 &&& 63 = x % 64 := by
      rw [h63, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 6 ∣ 4294967296)]
    simp [this]
    omega
  rw [BitVec.toNat_sub, h]
  simp
  omega

theorem sum2 (s : State) (y3 : Nat) (x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220 : Nat)
    (S : State) (h : PC_14c_1f3 s y3 x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220 S)
    (hst : Start14c s y3 x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220)
    (hb : x14cm218 < 2 ^ 64) :
    ∃ x160rcx x1f3rax x1f3r10 x1f3mb0, L1f3 s S x1f3rax x160rcx x14crsi x14crdi x14cr8 x14cr9 x1f3r10 x1f3mb0 x14cm208 x14cm210 x14cm218 x14cm220 ∧ RecRegs s S ∧ RecMem s S.mem y3 ∧
      x160rcx = (x14crcx % 64 + 18446744073709551615) % 18446744073709551616 ∧ x1f3mb0 = x1f3rax ∧
      x1f3rax + 18446744073709551616 * x1f3r10 = (if ((2 * (r1c x14crax x14crdx * 18446744073709551616) + 2 ^ 128 - (2 * stage2e (r1c x14crax x14crdx) x14cm218 y3) % 2 ^ 128) % 2 ^ 128 = 0 ∧ x14crbx = 0) then 2 ^ 128 - 1 else (2 * (r1c x14crax x14crdx * 18446744073709551616) + 2 ^ 128 - (2 * stage2e (r1c x14crax x14crdx) x14cm218 y3) % 2 ^ 128) % 2 ^ 128) := by
  unfold PC_14c_1f3 at h
  obtain ⟨x160rax, x160rcx, x1c1rax, x1c1rdx, x1c1r10, x1d0r10, x1d0r11, x1f3rax, x1f3r10, x1f3mb0, hLz, h_x160rax, h_x160rcx, h_x1c1rax, h_x1c1rdx, h_x1c1r10, h_x1d0r10, h_x1d0r11, h_x1f3rax, h_x1f3r10, h_x1f3mb0, hRz, hMz⟩ := h
  obtain ⟨hax, hbx, hdx, hsi, hm220, hdi, h8, h9, hcx, hY, h63, hlt⟩ := hst
  have M64 : (0 : Nat) < 2 ^ 64 := by decide
  have hbx_lt : x14crbx < 2 ^ 64 := by rw [hbx]; exact Nat.mod_lt _ M64
  have hax_lt : x14crax < 2 ^ 64 := by rw [hax]; exact Nat.mod_lt _ M64
  have hdx_lt : x14crdx < 2 ^ 64 := by rw [hdx]; exact Nat.or_lt_two_pow hax_lt hbx_lt
  have hr1 : x160rax = r1c x14crax x14crdx := by
    rw [h_x160rax]; unfold r1c; split
    · rfl
    · simp [Nat.mod_eq_of_lt hax_lt]
  have hr1lt : x160rax < 2 ^ 64 := by
    rw [hr1]; unfold r1c; split
    · decide
    · exact hax_lt
  rw [hsi, hdi] at h_x1c1rax h_x1c1rdx
  have hlx : x1c1rax < 2 ^ 64 := by rw [h_x1c1rax]; exact Nat.mod_lt _ M64
  have hhx : x1c1rdx < 2 ^ 64 := by rw [h_x1c1rdx]; exact Nat.mod_lt _ M64
  have he : x1c1rax + 2 ^ 64 * x1c1rdx = stage2e x160rax x14cm218 y3 := by
    rw [h_x1c1rax, h_x1c1rdx]; unfold stage2e; janus_carry
  have hr10 : x1c1r10 = x160rax := by rw [h_x1c1r10]; exact Nat.mod_eq_of_lt hr1lt
  rw [hr10, pos_toNat _ (by omega)] at h_x1d0r10
  have hlo : x1d0r11 < 2 ^ 64 := by rw [h_x1d0r11]; exact Nat.mod_lt _ M64
  have hhi : x1d0r10 < 2 ^ 64 := by rw [h_x1d0r10]; exact Nat.mod_lt _ M64
  have hsub : (x1d0r11 + 2 ^ 64 * x1d0r10 + 2 * (x1c1rax + 2 ^ 64 * x1c1rdx)) % 2 ^ 128 = (2 * (x160rax * 2 ^ 64)) % 2 ^ 128 := by
    rw [h_x1d0r11, h_x1d0r10]; janus_carry
  rw [he, hr1] at hsub
  have hor : ∀ a b c : Nat, a < 2 ^ 64 → b < 2 ^ 64 → c < 2 ^ 64 →
      (BitVec.ofNat 64 a ||| (BitVec.ofNat 64 b ||| BitVec.ofNat 64 c)).toNat = a ||| (b ||| c) := by
    intro a b c ha hb hc
    simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc]
  rw [hor _ _ _ hbx_lt hlo hhi] at h_x1f3rax h_x1f3r10 h_x1f3mb0
  have hzero : (x14crbx ||| (x1d0r11 ||| x1d0r10)) = 0 ↔ x14crbx = 0 ∧ x1d0r11 = 0 ∧ x1d0r10 = 0 := by
    simp [Nat.or_eq_zero_iff]
  refine ⟨x160rcx, x1f3rax, x1f3r10, x1f3mb0, ?_, hRz, hMz, ?_, ?_, ?_⟩
  · exact hLz
  · rw [h_x160rcx]; exact rcx_bv _
  · rw [h_x1f3mb0, h_x1f3rax]
    split
    · simp
    · simp [Nat.mod_eq_of_lt hlo]
  · have hs0 : (x1d0r11 + 2 ^ 64 * x1d0r10 + 2 * stage2e (r1c x14crax x14crdx) x14cm218 y3) % 2 ^ 128 = (2 * (r1c x14crax x14crdx * 2 ^ 64)) % 2 ^ 128 := hsub
    by_cases hc : x14crbx ||| (x1d0r11 ||| x1d0r10) = 0
    · obtain ⟨h1, h2, h3⟩ := hzero.1 hc
      rw [if_pos hc] at h_x1f3rax h_x1f3r10
      have e1 : x1f3rax = 2 ^ 64 - 1 := by rw [h_x1f3rax]; decide
      have e2 : x1f3r10 = 2 ^ 64 - 1 := by rw [h_x1f3r10]; decide
      rw [h2, h3] at hs0
      have hraw : (2 * (r1c x14crax x14crdx * 18446744073709551616) + 2 ^ 128 - (2 * stage2e (r1c x14crax x14crdx) x14cm218 y3) % 2 ^ 128) % 2 ^ 128 = 0 := by
        omega
      rw [if_pos ⟨hraw, h1⟩, e1, e2]
    · rw [if_neg hc] at h_x1f3rax h_x1f3r10
      have hR2 : x1f3rax + 18446744073709551616 * x1f3r10 = x1d0r11 + 2 ^ 64 * x1d0r10 := by
        rw [h_x1f3rax, h_x1f3r10]
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi]
      have hnz : ¬ ((2 * (r1c x14crax x14crdx * 18446744073709551616) + 2 ^ 128 - (2 * stage2e (r1c x14crax x14crdx) x14cm218 y3) % 2 ^ 128) % 2 ^ 128 = 0 ∧ x14crbx = 0) := by
        rintro ⟨h0, h1⟩
        apply hc
        have hlo0 : x1d0r11 = 0 := by omega
        have hhi0 : x1d0r10 = 0 := by omega
        exact hzero.2 ⟨h1, hlo0, hhi0⟩
      rw [if_neg hnz, hR2]
      omega

end Fv256.Amd64.RecipSeg
