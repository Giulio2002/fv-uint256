import Fv256.Proofs.Arm64.RecipG.G_108_16c
import Fv256.Proofs.Arm64.RecipBridge
import Fv256.Proofs.Common.UtilAM
import Fv256.Proofs.Arm64.RecipBv
import Janus.Tactic.CarryNf

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.RecipSeg
open Fv256.F Fv256.RecipMath

def s2HI (r el eh : Nat) : Nat := ((r + (18446744073709551616 - 1 - eh) + (0 + 18446744073709551616 - el) / 18446744073709551616) % 18446744073709551616 +
        (r + (18446744073709551616 - 1 - eh) + (0 + 18446744073709551616 - el) / 18446744073709551616) % 18446744073709551616 +
        ((18446744073709551616 - el) % 18446744073709551616 + (18446744073709551616 - el) % 18446744073709551616) / 18446744073709551616) % 18446744073709551616

def s2LO (el : Nat) : Nat := (18446744073709551616 - el + (18446744073709551616 - el)) % 18446744073709551616

/-- the 128-bit sub/double of stage 2, on the abstract words `el`, `eh` of `e` -/
theorem s2fin (r el eh y3 : Nat) (hr : r < 2 ^ 64) (hel : el < 2 ^ 64) (heh : eh < 2 ^ 64) (hy : y3 < 2 ^ 64) :
    s2LO el + 2 ^ 64 * s2HI r el eh = (2 * (r * 2 ^ 64) + 2 ^ 128 - (2 * (el + 2 ^ 64 * eh)) % 2 ^ 128) % 2 ^ 128 ∧
    ((s2HI r el eh ||| s2LO el ||| y3 * 2 % 18446744073709551616) = 0 ↔
      ((2 * (r * 2 ^ 64) + 2 ^ 128 - (2 * (el + 2 ^ 64 * eh)) % 2 ^ 128) % 2 ^ 128 = 0 ∧ 2 * y3 % 2 ^ 64 = 0)) := by
  have h1 : s2LO el + 2 ^ 64 * s2HI r el eh = (2 * (r * 2 ^ 64) + 2 ^ 128 - (2 * (el + 2 ^ 64 * eh)) % 2 ^ 128) % 2 ^ 128 := by
    unfold s2LO s2HI; omega
  have hLO : s2LO el < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hHI : s2HI r el eh < 2 ^ 64 := Nat.mod_lt _ (by decide)
  refine ⟨h1, ?_⟩
  rw [Nat.or_assoc, Nat.or_eq_zero_iff, Nat.or_eq_zero_iff]
  constructor
  · rintro ⟨a, b, c⟩
    refine ⟨by rw [← h1]; omega, by omega⟩
  · rintro ⟨a, b⟩
    refine ⟨by omega, by omega, by omega⟩

def s2EL (r y2 y3 : Nat) : Nat := ((y3 * (r * r / 2 ^ 64) % 2 ^ 64 + r * r % 2 ^ 64 * y3 / 2 ^ 64 + (r * r * y3 % 2 ^ 64 + y2 * (r * r % 2 ^ 64) / 2 ^ 64) / 2 ^ 64) % 2 ^ 64 + y2 * (r * r / 2 ^ 64) / 2 ^ 64 + (y2 * (r * r / 2 ^ 64) % 2 ^ 64 + (r * r * y3 + y2 * (r * r % 2 ^ 64) / 2 ^ 64) % 2 ^ 64) / 2 ^ 64) % 2 ^ 64

def s2EH (r y2 y3 : Nat) : Nat := (y3 * (r * r / 2 ^ 64) / 2 ^ 64 + (y3 * (r * r / 2 ^ 64) % 2 ^ 64 + r * r % 2 ^ 64 * y3 / 2 ^ 64 + (r * r * y3 % 2 ^ 64 + y2 * (r * r % 2 ^ 64) / 2 ^ 64) / 2 ^ 64) / 2 ^ 64 + ((y3 * (r * r / 2 ^ 64) % 2 ^ 64 + r * r % 2 ^ 64 * y3 / 2 ^ 64 + (r * r * y3 % 2 ^ 64 + y2 * (r * r % 2 ^ 64) / 2 ^ 64) / 2 ^ 64) % 2 ^ 64 + y2 * (r * r / 2 ^ 64) / 2 ^ 64 + (y2 * (r * r / 2 ^ 64) % 2 ^ 64 + (r * r * y3 + y2 * (r * r % 2 ^ 64) / 2 ^ 64) % 2 ^ 64) / 2 ^ 64) / 2 ^ 64) % 2 ^ 64

theorem s2he (r y2 y3 : Nat) (hr : r < 2 ^ 64) (h2 : y2 < 2 ^ 64) (h3 : y3 < 2 ^ 64) : s2EL r y2 y3 + 2 ^ 64 * s2EH r y2 y3 = stage2e r y2 y3 := by
  unfold s2EL s2EH stage2e; janus_carry

theorem sum2 (s S : State) (x108r0 x108r1 x108r2 x108r3 x108r4 x108r5 x108m176 x108m240 x108m248 x108m256 : Nat)
    (h : P_108_16c s x108r0 x108r1 x108r2 x108r3 x108r4 x108r5 x108m176 x108m240 x108m248 x108m256 S)
    (b0 : x108r0 < 2 ^ 64) (b1 : x108r1 = 2 ^ 64 - 1) (b2 : x108r2 < 2 ^ 64) (b3 : x108r3 < 2 ^ 64) :
    ∃ x16cr0 x16cr7, L16c S x16cr0 x108r2 x108r3 x108r4 x108r5 x16cr7 0 x108m176 x108m240 x108m248 x108m256 ∧
      x16cr7 + 2 ^ 64 * x16cr0 = (if ((2 * (x108r0 * 2 ^ 64) + 2 ^ 128 - (2 * stage2e x108r0 x108r2 x108r3) % 2 ^ 128) % 2 ^ 128 = 0 ∧ 2 * x108r3 % 2 ^ 64 = 0)
        then 2 ^ 128 - 1 else (2 * (x108r0 * 2 ^ 64) + 2 ^ 128 - (2 * stage2e x108r0 x108r2 x108r3) % 2 ^ 128) % 2 ^ 128) ∧
      RecRegs s S ∧ RecMem s S.mem := by
  unfold P_108_16c at h
  obtain ⟨x16cr0, x16cr7, hL, h_x16cr0, h_x16cr7, hR, hM⟩ := h
  refine ⟨x16cr0, x16cr7, hL, ?_, hR, hM⟩
  simp (disch := first | janus_carry_disch | decide | omega) only [Fv256.AM.dec_le_div, Bool.toNat_true, Bool.toNat_false, Nat.reducePow] at h_x16cr0 h_x16cr7
  clear hL hR hM
  have k := s2fin x108r0 (s2EL x108r0 x108r2 x108r3) (s2EH x108r0 x108r2 x108r3) x108r3 b0 (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) b3
  obtain ⟨k1, k2⟩ := k
  have e0 : x16cr0 = if (s2HI x108r0 (s2EL x108r0 x108r2 x108r3) (s2EH x108r0 x108r2 x108r3) ||| s2LO (s2EL x108r0 x108r2 x108r3) ||| x108r3 * 2 % 18446744073709551616) = 0 then x108r1 else s2HI x108r0 (s2EL x108r0 x108r2 x108r3) (s2EH x108r0 x108r2 x108r3) := h_x16cr0
  have e7 : x16cr7 = if (s2HI x108r0 (s2EL x108r0 x108r2 x108r3) (s2EH x108r0 x108r2 x108r3) ||| s2LO (s2EL x108r0 x108r2 x108r3) ||| x108r3 * 2 % 18446744073709551616) = 0 then x108r1 else s2LO (s2EL x108r0 x108r2 x108r3) := h_x16cr7
  rw [← s2he _ _ _ b0 b2 b3]
  rw [e0, e7]
  by_cases hc : (s2HI x108r0 (s2EL x108r0 x108r2 x108r3) (s2EH x108r0 x108r2 x108r3) ||| s2LO (s2EL x108r0 x108r2 x108r3) ||| x108r3 * 2 % 18446744073709551616) = 0
  · have hc' := k2.1 hc
    rw [if_pos hc, if_pos hc, if_pos hc', b1]
  · have hc' : ¬ _ := fun h => hc (k2.2 h)
    rw [if_neg hc, if_neg hc, if_neg hc']; omega

end Fv256.Arm64.RecipSeg
