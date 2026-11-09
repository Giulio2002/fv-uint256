import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.RlpSpec
import Fv256.Proofs.Common.RlpLemmas

/-!
# `EncodeRLP`: the bytes of the multi-byte encoding (ISA independent, no extraction)

The compiled code allocates a `[33]byte`, stores the four 64-bit limbs of `*z` byte-reversed (`BSWAP`) at offsets
`1, 9, 17, 25`, the prefix `0x80 + n` at offset `32 - n`, and writes the slice `[32 - n, 33)`.
-/

open Janus.Arm64

namespace Fv256.Rlp

theorem revB_lt (k x : Nat) : revBytesNat k x < 256 ^ k := by
  induction k generalizing x with
  | zero => simp [revBytesNat]
  | succ k ih =>
    unfold revBytesNat
    have h1 : x % 256 < 256 := Nat.mod_lt _ (by decide)
    have h2 := ih (x / 256)
    rw [Nat.pow_succ]
    have : (x % 256) * 256 ^ k + revBytesNat k (x / 256) < 256 * 256 ^ k := by
      have : (x % 256) * 256 ^ k ≤ 255 * 256 ^ k := Nat.mul_le_mul_right _ (by omega)
      omega
    omega

theorem revBytes_byte (k : Nat) : ∀ (x i : Nat), i < k → revBytesNat k x / 256 ^ i % 256 = x / 256 ^ (k - 1 - i) % 256 := by
  induction k with
  | zero => intro x i h; omega
  | succ k ih =>
    intro x i hi
    have hR : revBytesNat k (x / 256) < 256 ^ k := revB_lt k _
    simp only [revBytesNat]
    by_cases hik : i = k
    · subst hik
      have : ((x % 256) * 256 ^ i + revBytesNat i (x / 256)) / 256 ^ i = x % 256 := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt hR, Nat.zero_add]
      rw [this]
      simp
    · have hlt : i < k := by omega
      have hk : 256 ^ k = 256 ^ i * 256 ^ (k - i) := by rw [← Nat.pow_add]; congr 1; omega
      have e : (x % 256) * 256 ^ k = 256 ^ i * ((x % 256) * 256 ^ (k - i)) := by
        rw [hk, Nat.mul_left_comm]
      have h1 : ((x % 256) * 256 ^ k + revBytesNat k (x / 256)) / 256 ^ i =
          ((x % 256) * 256 ^ (k - i)) + revBytesNat k (x / 256) / 256 ^ i := by
        rw [e, Nat.mul_add_div (Nat.pow_pos (by decide))]
      have h2 : ((x % 256) * 256 ^ (k - i)) % 256 = 0 := by
        obtain ⟨d, hd⟩ : ∃ d, k - i = d + 1 := ⟨k - i - 1, by omega⟩
        rw [hd, Nat.pow_succ, ← Nat.mul_assoc]
        exact Nat.mul_mod_left _ _
      rw [h1, Nat.add_mod, h2, Nat.zero_add, Nat.mod_mod, ih (x / 256) i hlt, Nat.div_div_eq_div_mul, ← Nat.pow_succ']
      congr 3
      omega

/-- the byte `q` of a 64-bit window of `v` -/
theorem win_byte (X l q : Nat) (hl : X % 18446744073709551616 = l) (hq : q < 8) :
    X / 256 ^ q % 256 = l / 256 ^ q % 256 := by
  rw [← hl, ← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (show 256 ^ q * 256 ∣ 18446744073709551616 from
      (show 256 ^ q * 256 = 256 ^ (q + 1) by rw [Nat.pow_succ]) ▸ (show 256 ^ (q + 1) ∣ 256 ^ 8 from Nat.pow_dvd_pow _ hq))]

theorem win_byte' (v p q l : Nat) (hl : v / 256 ^ (8 * p) % 18446744073709551616 = l) (hq : q < 8) :
    v / 256 ^ (8 * p + q) % 256 = l / 256 ^ q % 256 := by
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]
  exact win_byte _ _ _ hl hq

theorem blk (v L p o a0 : Nat) (hL : v / 256 ^ (8 * p) % 18446744073709551616 = L) (ha : a0 ≤ o) (ho : o < a0 + 8)
    (hp : 32 - o = 8 * p + (7 - (o - a0))) :
    (BitVec.ofNat 8 (revBytesNat 8 L / 256 ^ (o - a0))).toNat = v / 256 ^ (32 - o) % 256 := by
  simp only [BitVec.toNat_ofNat, Nat.reducePow]
  rw [hp, win_byte' v p (7 - (o - a0)) L hL (by omega)]
  have := revBytes_byte 8 L (o - a0) (by omega)
  rw [this]

/-- the memory after the four `BSWAP` stores of the limbs of `v = l0 + 2^64 l1 + 2^128 l2 + 2^192 l3` into the object at `obj` -/
def bswapChain (m : Memory) (obj l0 l1 l2 l3 : Nat) : Memory :=
  (((m.writeLE (obj + 1) 8 (revBytesNat 8 l3)).writeLE (obj + 9) 8 (revBytesNat 8 l2)).writeLE (obj + 17) 8
    (revBytesNat 8 l1)).writeLE (obj + 25) 8 (revBytesNat 8 l0)

theorem bswap_byte (m : Memory) (obj l0 l1 l2 l3 o : Nat) (h0 : l0 < 2 ^ 64) (h1 : l1 < 2 ^ 64) (h2 : l2 < 2 ^ 64)
    (h3 : l3 < 2 ^ 64) (ho1 : 1 ≤ o) (ho2 : o ≤ 32) :
    ((bswapChain m obj l0 l1 l2 l3).bytes (obj + o)).toNat =
      (l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3) / 256 ^ (32 - o) % 256 := by
  simp only [bswapChain, Memory.bytes_writeLE]
  have e0 : (l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3) / 256 ^ (8 * 0) % 18446744073709551616 = l0 := by
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]; omega
  have e1 : (l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3) / 256 ^ (8 * 1) % 18446744073709551616 = l1 := by
    simp only [Nat.reducePow, Nat.reduceMul]; omega
  have e2 : (l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3) / 256 ^ (8 * 2) % 18446744073709551616 = l2 := by
    simp only [Nat.reducePow, Nat.reduceMul]; omega
  have e3 : (l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3) / 256 ^ (8 * 3) % 18446744073709551616 = l3 := by
    simp only [Nat.reducePow, Nat.reduceMul]; omega
  by_cases c0 : 25 ≤ o
  · rw [if_pos (by omega), show obj + o - (obj + 25) = o - 25 by omega]
    exact blk _ _ 0 o 25 e0 c0 (by omega) (by omega)
  rw [if_neg (by omega)]
  by_cases c1 : 17 ≤ o
  · rw [if_pos (by omega), show obj + o - (obj + 17) = o - 17 by omega]
    exact blk _ _ 1 o 17 e1 c1 (by omega) (by omega)
  rw [if_neg (by omega)]
  by_cases c2 : 9 ≤ o
  · rw [if_pos (by omega), show obj + o - (obj + 9) = o - 9 by omega]
    exact blk _ _ 2 o 9 e2 c2 (by omega) (by omega)
  rw [if_neg (by omega)]
  rw [if_pos (by omega), show obj + o - (obj + 1) = o - 1 by omega]
  exact blk _ _ 3 o 1 e3 ho1 (by omega) (by omega)

/-- the multi-byte encoding: the slice `[obj + 32 - nB, obj + 33)` of the object after the prefix store -/
theorem pm_str (m : Memory) (obj l0 l1 l2 l3 nB c : Nat) (h0 : l0 < 2 ^ 64) (h1 : l1 < 2 ^ 64) (h2 : l2 < 2 ^ 64)
    (h3 : l3 < 2 ^ 64) (hb8 : 7 < Spec.bitLen (l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3))
    (hnb : nB = (Spec.bitLen (l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3) + 7) / 8) (hn1 : 1 ≤ nB) (hn32 : nB ≤ 32)
    (hc : c % 256 = 0x80 + nB) :
    Janus.Spec.strBytes ((bswapChain m obj l0 l1 l2 l3).writeLE (obj + (32 - nB)) 1 c) (obj + (32 - nB)) (nB + 1) =
      rlpBytes (l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3) := by
  have hv0 : l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3 ≠ 0 := fun h => by simp [Spec.bitLen, h] at hb8
  unfold rlpBytes
  rw [if_neg hv0, if_neg (by omega), ← hnb]
  unfold Janus.Spec.strBytes
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp only [Function.comp, Nat.add_zero, Memory.bytes_writeLE, ite_true, Nat.sub_self, Nat.pow_zero, Nat.div_one,
      BitVec.toNat_ofNat, Nat.reducePow, hc]
    simp
    omega
  · apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    simp only [Function.comp, Memory.bytes_writeLE]
    rw [if_neg (by omega), show obj + (32 - nB) + (k + 1) = obj + (32 - nB + (k + 1)) by omega,
      bswap_byte m obj l0 l1 l2 l3 _ h0 h1 h2 h3 (by omega) (by omega)]
    congr 3
    omega

theorem rlpBytes_length_multi (v : Nat) (h8 : 7 < Spec.bitLen v) :
    (rlpBytes v).length = (Spec.bitLen v + 7) / 8 + 1 := by
  have hv0 : v ≠ 0 := fun h => by simp [Spec.bitLen, h] at h8
  unfold rlpBytes
  rw [if_neg hv0, if_neg (by omega)]
  simp

/-- the length `33 - DI` of the slice, as the compiled code computes it -/
theorem pm_len (v bl nB : Nat) (hbl : Spec.bitLen v = bl) (h8 : 7 < bl) (hnb : nB = (bl + 7) / 8) (h32 : nB ≤ 32) :
    18446744073709551616 - (18446744073709551583 + (4294967296 - (18446744073709551584 + nB) % 4294967296) % 256 % 4294967296) =
      (rlpBytes v).length := by
  rw [rlpBytes_length_multi v (by omega), hbl]
  omega

/-- the multi-byte slice, with the offset and the prefix byte as the compiled code computes them -/
theorem pm_str2 (m : Memory) (obj l0 l1 l2 l3 v bl nB : Nat) (h0 : l0 < 2 ^ 64) (h1 : l1 < 2 ^ 64) (h2 : l2 < 2 ^ 64)
    (h3 : l3 < 2 ^ 64) (hv : v = l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3) (hbl : Spec.bitLen v = bl) (h8 : 7 < bl)
    (hnb : nB = (bl + 7) / 8) (h32 : nB ≤ 32) :
    Janus.Spec.strBytes
      (((((m.writeLE (obj + 1) 8 (revBytesNat 8 l3)).writeLE (obj + 9) 8 (revBytesNat 8 l2)).writeLE (obj + 17) 8
        (revBytesNat 8 l1)).writeLE (obj + 25) 8 (revBytesNat 8 l0)).writeLE
        (obj + (4294967296 - (18446744073709551584 + nB) % 4294967296) % 256 % 4294967296) 1
        ((18446744073709551488 + nB) % 256))
      (obj + (4294967296 - (18446744073709551584 + nB) % 4294967296) % 256 % 4294967296)
      (18446744073709551616 - (18446744073709551583 +
        (4294967296 - (18446744073709551584 + nB) % 4294967296) % 256 % 4294967296)) = rlpBytes v := by
  subst hv
  have hD : (4294967296 - (18446744073709551584 + nB) % 4294967296) % 256 % 4294967296 = 32 - nB := by omega
  have hN : 18446744073709551616 - (18446744073709551583 +
        (4294967296 - (18446744073709551584 + nB) % 4294967296) % 256 % 4294967296) = nB + 1 := by omega
  rw [hN, hD]
  exact pm_str m obj l0 l1 l2 l3 nB _ h0 h1 h2 h3 (by omega) (by omega) (by omega) (by omega) (by omega)

theorem pm_str3 (m : Memory) (obj l0 l1 l2 l3 v bl nB : Nat) (h0 : l0 < 2 ^ 64) (h1 : l1 < 2 ^ 64) (h2 : l2 < 2 ^ 64)
    (h3 : l3 < 2 ^ 64) (hv : v = l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3) (hbl : Spec.bitLen v = bl) (h8 : 7 < bl)
    (hnb : nB = (bl + 7) / 8) (h32 : nB ≤ 32) :
    Janus.Spec.strBytes
      (((((m.writeLE (obj + 1) 8 (revBytesNat 8 l3)).writeLE (obj + 9) 8 (revBytesNat 8 l2)).writeLE (obj + 17) 8
        (revBytesNat 8 l1)).writeLE (obj + 25) 8 (revBytesNat 8 l0)).writeLE
        (obj + (4294967296 - (18446744073709551584 + nB) % 4294967296) % 256 % 4294967296) 1
        ((18446744073709551488 + nB) % 256))
      (obj + (4294967296 - (18446744073709551584 + nB) % 4294967296) % 256 % 4294967296)
      (rlpBytes v).length = rlpBytes v := by
  rw [← pm_len v bl nB hbl h8 hnb h32]
  exact pm_str2 m obj l0 l1 l2 l3 v bl nB h0 h1 h2 h3 hv hbl h8 hnb h32

set_option maxRecDepth 100000 in
theorem nB_bv (bl : Nat) (h : bl ≤ 256) :
    (BitVec.sshiftRight (BitVec.ofNat 64 bl + BitVec.sshiftRight (BitVec.ofNat 64 bl + 7#64) 63 >>> 61 + 7#64) 3).toNat =
      (bl + 7) / 8 := by
  have : ∀ b : Fin 257, (BitVec.sshiftRight (BitVec.ofNat 64 b.val + BitVec.sshiftRight (BitVec.ofNat 64 b.val + 7#64) 63 >>> 61 + 7#64) 3).toNat = (b.val + 7) / 8 := by
    decide
  exact this ⟨bl, by omega⟩

set_option maxRecDepth 100000 in
theorem nB_bv2 (bl : Nat) (h : bl ≤ 256) :
    BitVec.sshiftRight (BitVec.ofNat 64 bl + BitVec.sshiftRight (BitVec.ofNat 64 bl + 7#64) 63 >>> 61 + 7#64) 3 =
      BitVec.ofNat 64 ((bl + 7) / 8) := by
  have : ∀ b : Fin 257, BitVec.sshiftRight (BitVec.ofNat 64 b.val + BitVec.sshiftRight (BitVec.ofNat 64 b.val + 7#64) 63 >>> 61 + 7#64) 3 =
      BitVec.ofNat 64 ((b.val + 7) / 8) := by
    decide
  exact this ⟨bl, by omega⟩

set_option maxRecDepth 100000 in
theorem D_bv (n : Nat) (h : n ≤ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.setWidth 64 (0#32 -
      BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n - 32#64))))))) =
      BitVec.ofNat 64 (32 - n) := by
  have : ∀ b : Fin 33, BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.setWidth 64 (0#32 -
      BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 b.val - 32#64))))))) =
      BitVec.ofNat 64 (32 - b.val) := by decide
  exact this ⟨n, by omega⟩

set_option maxRecDepth 100000 in
theorem E_bv (n : Nat) (h : n ≤ 32) :
    0#64 - (BitVec.ofNat 64 (32 - n) - 33#64) = BitVec.ofNat 64 (n + 1) := by
  have : ∀ b : Fin 33, 0#64 - (BitVec.ofNat 64 (32 - b.val) - 33#64) = BitVec.ofNat 64 (b.val + 1) := by decide
  exact this ⟨n, by omega⟩

/-- the object after the four `BSWAP` stores and the prefix byte, as the amd64 code leaves it -/
abbrev pmChain (M : Memory) (obj l0 l1 l2 l3 nB : Nat) : Memory :=
  ((((M.writeLE (obj + 1) 8 (revBytesNat 8 l3)).writeLE (obj + 9) 8 (revBytesNat 8 l2)).writeLE (obj + 17) 8
    (revBytesNat 8 l1)).writeLE (obj + 25) 8 (revBytesNat 8 l0)).writeLE (obj + (32 - nB)) 1
    ((18446744073709551488 + nB) % 256)

theorem pm_rlpVal (M : Memory) (obj l0 l1 l2 l3 nB a v zz : Nat) (hn : nB ≤ 32) (h1 : zz + 32 ≤ obj ∨ obj + 33 ≤ zz)
    (h2 : a + 8 ≤ zz ∨ zz + 32 ≤ a) :
    rlpVal ((pmChain M obj l0 l1 l2 l3 nB).writeLE a 8 v) zz = rlpVal M zz := by
  simp only [pmChain]
  rw [rlpVal_write_out _ _ _ _ _ h2, rlpVal_write_out _ _ _ _ _ (by omega), rlpVal_write_out _ _ _ _ _ (by omega),
    rlpVal_write_out _ _ _ _ _ (by omega), rlpVal_write_out _ _ _ _ _ (by omega), rlpVal_write_out _ _ _ _ _ (by omega)]

theorem pm_strOut (M : Memory) (obj l0 l1 l2 l3 nB a v : Nat) (h : a + 8 ≤ obj ∨ obj + 33 ≤ a) (hn : nB ≤ 32) :
    Janus.Spec.strBytes ((pmChain M obj l0 l1 l2 l3 nB).writeLE a 8 v) (obj + (32 - nB)) (nB + 1) =
      Janus.Spec.strBytes (pmChain M obj l0 l1 l2 l3 nB) (obj + (32 - nB)) (nB + 1) :=
  strBytes_write_out _ _ _ _ _ _ (by omega)

end Fv256.Rlp
