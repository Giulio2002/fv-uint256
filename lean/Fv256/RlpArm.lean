import Fv256.RlpBytes

/-!
# `EncodeRLP` arm64: the arithmetic of the compiled slice offset, length and prefix byte (no extraction)

The compiled code computes `n = (bits + 7) / 8` with `ADD`/`ASR`/`ADD R2>>61`, the offset `32 - n` with `SUB R1->3` and the
prefix byte `n - 128` (`ASR`, `SUB`); as `BitVec` terms they are `XA`, `DA`, `CA`, `NA` below (the forms `janus_run` produces).
-/

open Janus.Arm64

namespace Fv256.Rlp

/-- `bits + (((bits + 7) >>s 63) >>> 61) + 7` -/
abbrev XA (bl : Nat) : BitVec 64 :=
  BitVec.ofNat 64 bl + (((if (BitVec.ofNat 64 bl + 7#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&&
    18446744073709551614#64 ||| (BitVec.ofNat 64 bl + 7#64).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 61) + 7#64

/-- the offset of the prefix byte in the object -/
abbrev DA (bl : Nat) : Nat := ((32#64 - (XA bl).sshiftRight 3).rotateRight 0).toNat % 256

/-- the prefix byte -/
abbrev CA (bl : Nat) : Nat :=
  (18446744073709551488 + ((if (XA bl).getLsbD 63 = true then 18446744073709551615#64 else 0#64).toNat &&&
    16140901064495857664 ||| ((XA bl).rotateRight 3).toNat % 2305843009213693952)) % 18446744073709551616

/-- the length of the slice -/
abbrev NA (bl : Nat) : Nat := (18446744073709551616 - DA bl + 33) % 18446744073709551616

theorem arm_chunk (k : Nat) (hk : k < 5) : ∀ b : Fin 64, 8 ≤ 64 * k + b.val → 64 * k + b.val ≤ 256 →
    DA (64 * k + b.val) = 32 - (64 * k + b.val + 7) / 8 ∧ NA (64 * k + b.val) = (64 * k + b.val + 7) / 8 + 1 ∧
      CA (64 * k + b.val) % 256 = 128 + (64 * k + b.val + 7) / 8 := by
  have : ∀ k : Fin 5, ∀ b : Fin 64, 8 ≤ 64 * k.val + b.val → 64 * k.val + b.val ≤ 256 →
      DA (64 * k.val + b.val) = 32 - (64 * k.val + b.val + 7) / 8 ∧ NA (64 * k.val + b.val) = (64 * k.val + b.val + 7) / 8 + 1 ∧
      CA (64 * k.val + b.val) % 256 = 128 + (64 * k.val + b.val + 7) / 8 := by
    decide +kernel
  exact this ⟨k, hk⟩

theorem arm_arith (bl : Nat) (h8 : 8 ≤ bl) (h256 : bl ≤ 256) :
    DA bl = 32 - (bl + 7) / 8 ∧ NA bl = (bl + 7) / 8 + 1 ∧ CA bl % 256 = 128 + (bl + 7) / 8 := by
  have h := arm_chunk (bl / 64) (by omega) ⟨bl % 64, by omega⟩ (by simp only []; omega) (by simp only []; omega)
  have e : 64 * (bl / 64) + bl % 64 = bl := by omega
  simp only [e] at h
  exact h

theorem rc8 (l : Nat) (h : l < 2 ^ 64) : revContainersNat 8 1 l = revBytesNat 8 l := by
  have h256 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  have e : l % 256 ^ 8 = l := Nat.mod_eq_of_lt (by omega)
  rw [revContainersNat, e]
  show revBytesNat 8 l + 256 ^ 8 * 0 = _
  omega

/-- the multi-byte slice as the arm64 code writes it -/
theorem pm_strA (m : Memory) (obj l0 l1 l2 l3 v bl : Nat) (h0 : l0 < 2 ^ 64) (h1 : l1 < 2 ^ 64) (h2 : l2 < 2 ^ 64)
    (h3 : l3 < 2 ^ 64) (hv : v = l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3) (hbl : Spec.bitLen v = bl) (h8 : 7 < bl)
    (h256 : bl ≤ 256) :
    Janus.Spec.strBytes
      (((((m.writeLE (obj + 1) 8 (revContainersNat 8 1 l3)).writeLE (obj + 9) 8 (revContainersNat 8 1 l2)).writeLE (obj + 17) 8
        (revContainersNat 8 1 l1)).writeLE (obj + 25) 8 (revContainersNat 8 1 l0)).writeLE (obj + DA bl) 1 (CA bl))
      (obj + DA bl) (NA bl) = rlpBytes v := by
  obtain ⟨hD, hN, hC⟩ := arm_arith bl (by omega) h256
  rw [rc8 _ h0, rc8 _ h1, rc8 _ h2, rc8 _ h3, hD, hN]
  subst hv
  exact pm_str m obj l0 l1 l2 l3 ((bl + 7) / 8) (CA bl) h0 h1 h2 h3 (by omega) (by omega) (by omega) (by omega) (by omega)

theorem pm_strA3 (m : Memory) (obj l0 l1 l2 l3 v bl : Nat) (h0 : l0 < 2 ^ 64) (h1 : l1 < 2 ^ 64) (h2 : l2 < 2 ^ 64)
    (h3 : l3 < 2 ^ 64) (hv : v = l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3) (hbl : Spec.bitLen v = bl) (h8 : 7 < bl)
    (h256 : bl ≤ 256) :
    Janus.Spec.strBytes
      (((((m.writeLE (obj + 1) 8 (revContainersNat 8 1 l3)).writeLE (obj + 9) 8 (revContainersNat 8 1 l2)).writeLE (obj + 17) 8
        (revContainersNat 8 1 l1)).writeLE (obj + 25) 8 (revContainersNat 8 1 l0)).writeLE (obj + DA bl) 1 (CA bl))
      (obj + DA bl) (rlpBytes v).length = rlpBytes v := by
  have hl : NA bl = (rlpBytes v).length := by
    rw [rlpBytes_length_multi v (by omega), hbl, (arm_arith bl (by omega) h256).2.1]
  rw [← hl]
  exact pm_strA m obj l0 l1 l2 l3 v bl h0 h1 h2 h3 hv hbl h8 h256

theorem pm_lenA (v bl : Nat) (hbl : Spec.bitLen v = bl) (h8 : 7 < bl) (h256 : bl ≤ 256) :
    NA bl = (rlpBytes v).length := by
  rw [rlpBytes_length_multi v (by omega), hbl, (arm_arith bl (by omega) h256).2.1]

theorem pm_strA4 (m : Memory) (obj l0 l1 l2 l3 v bl : Nat) (h0 : l0 < 2 ^ 64) (h1 : l1 < 2 ^ 64) (h2 : l2 < 2 ^ 64)
    (h3 : l3 < 2 ^ 64) (hv : v = l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3) (hbl : Spec.bitLen v = bl) (h8 : 7 < bl)
    (h256 : bl ≤ 256) :
    Janus.Spec.strBytes
      (((((m.writeLE (obj + 1) 8 (revContainersNat 8 1 l3)).writeLE (obj + 9) 8 (revContainersNat 8 1 l2)).writeLE (obj + 17) 8
        (revContainersNat 8 1 l1)).writeLE (obj + 25) 8 (revContainersNat 8 1 l0)).writeLE
        (obj + (32 - (bl + 7) / 8)) 1 (CA bl))
      (obj + (32 - (bl + 7) / 8)) ((bl + 7) / 8 + 1) = rlpBytes v := by
  obtain ⟨hD, hN, hC⟩ := arm_arith bl (by omega) h256
  rw [rc8 _ h0, rc8 _ h1, rc8 _ h2, rc8 _ h3]
  subst hv
  exact pm_str m obj l0 l1 l2 l3 ((bl + 7) / 8) (CA bl) h0 h1 h2 h3 (by omega) (by omega) (by omega) (by omega) (by omega)

theorem arm_norm (bl : Nat) (h8 : 8 ≤ bl) (h256 : bl ≤ 256) :
    (32 - (bl + 7) / 8) % 256 = 32 - (bl + 7) / 8 ∧
    (18446744073709551616 - (32 - (bl + 7) / 8) + 33) % 18446744073709551616 = (bl + 7) / 8 + 1 := by
  omega

theorem pm_lenB (v bl : Nat) (hbl : Spec.bitLen v = bl) (h8 : 7 < bl) :
    (rlpBytes v).length = (bl + 7) / 8 + 1 := by
  rw [rlpBytes_length_multi v (by omega), hbl]

end Fv256.Rlp
