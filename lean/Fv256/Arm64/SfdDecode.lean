import Fv256.Spec
import Fv256.Util
import Fv256.UtilI
import Fv256.Arm64.SfdProg

/-!
# `runtime.decoderune(s, k)` (arm64), as a callee of `SetFromDecimal`

`SetFromDecimal` strips leading zeros with `for i, c := range s { if c != '0' { break } }`; for a byte `>= 0x80`
the compiled `range` calls `runtime.decoderune`.  All that the caller needs: the decoded rune is never `'0'`
(it is `>= 0x80`: a decoded multi-byte rune is `> 0x7f` and the error rune is `U+FFFD`).  Proved by running the code on
the library program `SfdProg.program` (no extraction).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SfdDecode

abbrev dr : Nat := segAddr Fv256.Arm64.SfdProg.program "runtime.decoderune"

def DecPre (p len k : BitVec 64) (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ GuardOK s 0 ∧ StackOK s 24 16 ∧
  s.regs 0 = p ∧ s.regs 1 = len ∧ s.regs 2 = k ∧ s.mem.accessible p.toNat len.toNat false = true ∧
  p.toNat + len.toNat ≤ 2 ^ 48 ∧ k.toNat < len.toNat ∧
  (p.toNat + len.toNat ≤ s.sp.toNat - 24 ∨ s.sp.toNat + 16 ≤ p.toNat)

def DecPost (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18 ∧
  128 ≤ (s'.regs 0).toNat ∧ (s'.regs 0).toNat < 2 ^ 32 ∧
  MemFrame s.mem s'.mem [(s.sp.toNat - 24, s.sp.toNat), (s.sp.toNat + 8, s.sp.toNat + 16)]

theorem mask_keep' (len k : BitVec 64) (hk : k.toNat < len.toNat) (hl : len.toNat < 2 ^ 63) :
    k.toNat &&& ((k - len).sshiftRight 63).toNat = k.toNat := by
  have h : k - len = 0#64 - (len - k) := by bv_omega
  have hd : (len - k).toNat = len.toNat - k.toNat := by rw [BitVec.toNat_sub]; omega
  rw [h, Nat.and_comm]
  exact Fv256.I.mask_keep (len - k) k (by omega) (by omega)

theorem rune4_lt (a b c d : BitVec 64) :
    (d &&& 63#64 ||| (a.rotateRight 46 &&& 1835008#64 &&& 2097151#64 ||| (b &&& 63#64) <<< 12 ||| (c &&& 63#64) <<< 6)).toNat
      < 2 ^ 21 := by
  have h6 : ∀ x : BitVec 64, (x &&& 63#64).toNat < 64 := fun x => by
    rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)
  have hsh : ∀ (x : BitVec 64) (k : Nat), k ≤ 12 → ((x &&& 63#64) <<< k).toNat < 2 ^ 21 := by
    intro x k hk
    have := h6 x
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
    · have : 64 * 2 ^ k ≤ 64 * 2 ^ 12 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hk)
      have h2 : (x &&& 63#64).toNat * 2 ^ k < 64 * 2 ^ k := Nat.mul_lt_mul_of_lt_of_le (h6 x) (Nat.le_refl _) (Nat.two_pow_pos k)
      omega
    · have : 64 * 2 ^ k ≤ 64 * 2 ^ 12 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hk)
      have h2 : (x &&& 63#64).toNat * 2 ^ k < 64 * 2 ^ k := Nat.mul_lt_mul_of_lt_of_le (h6 x) (Nat.le_refl _) (Nat.two_pow_pos k)
      omega
  simp only [BitVec.toNat_or]
  refine Nat.or_lt_two_pow (by have := h6 d; omega) (Nat.or_lt_two_pow (Nat.or_lt_two_pow ?_ (hsh b 12 (by omega))) (hsh c 6 (by omega)))
  rw [BitVec.toNat_and]
  exact Nat.and_lt_two_pow _ (by decide)

theorem gt32 (E c : BitVec 32) (hE : E.toNat < 2^31) (hc : c.toNat < 2^31)
    (h : ¬((addSub E c true).snd.n == (addSub E c true).snd.v && !decide (E.toNat = c.toNat)) = false) :
    c.toNat < E.toNat := by
  simp only [addSub, addWithCarry, BitVec.msb_eq_decide, BitVec.toInt_eq_toNat_cond] at h
  simp only [BitVec.toNat_not, BitVec.toNat_ofNat, Bool.toNat_true] at h
  simp at h
  obtain ⟨h, hne⟩ := h
  have h1 : 2 * E.toNat < 4294967296 := by omega
  have h2 : ¬ 2 * (4294967295 - c.toNat) < 4294967296 := by omega
  simp only [h1, h2, if_true, if_false] at h
  by_cases hlt : c.toNat < E.toNat
  · exact hlt
  exfalso
  have hle : E.toNat ≤ c.toNat := by omega
  have hlt' : E.toNat < c.toNat := by omega
  have h3 : (E.toNat + (4294967295 - c.toNat) + 1) % 4294967296 = 4294967296 - (c.toNat - E.toNat) := by omega
  have h4 : ¬ 2 * ((E.toNat + (4294967295 - c.toNat) + 1) % 4294967296) < 4294967296 := by omega
  simp only [h4, if_false] at h
  have hA : 2147483648 ≤ (E.toNat + (4294967295 - c.toNat) + 1) % 4294967296 := by omega
  have hB : ((↑E.toNat + ↑(4294967295 - c.toNat) + 1 : Int) % 4294967296 - 4294967296) =
      ↑E.toNat + (↑(4294967295 - c.toNat) - 4294967296) + 1 := by omega
  rw [hB] at h
  simp [hA] at h

theorem h6lt (x : BitVec 64) : (x &&& 63#64).toNat < 64 := by
  rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)

theorem shl_lt (x : BitVec 64) (m k n : Nat) (hx : x.toNat < 2 ^ m) (hk : m + k ≤ n) (hn : n ≤ 63) :
    (x <<< k).toNat < 2 ^ n := by
  have h2 : 2 ^ (m + k) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hk
  have h3 : 2 ^ n ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) hn
  have h4 : x.toNat * 2 ^ k < 2 ^ m * 2 ^ k := Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_refl _) (Nat.two_pow_pos k)
  rw [Nat.pow_add] at h2
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
  · omega
  · have : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
    omega

theorem rune3_lt (a b c : BitVec 64) :
    (a.rotateRight 52 &&& 61440#64 &&& 65535#64 ||| (b &&& 63#64) <<< 6 ||| c &&& 63#64).toNat < 2 ^ 16 := by
  simp only [BitVec.toNat_or]
  have h1 := shl_lt (b &&& 63#64) 6 6 16 (by have := h6lt b; omega) (by omega) (by omega)
  refine Nat.or_lt_two_pow (Nat.or_lt_two_pow ?_ h1) (by have := h6lt c; omega)
  rw [BitVec.toNat_and]
  exact Nat.and_lt_two_pow _ (by decide)

theorem rune2_lt (a b : BitVec 64) :
    (b &&& 63#64 ||| (a &&& 31#64) <<< 6).toNat < 2 ^ 11 := by
  simp only [BitVec.toNat_or]
  have h1 := shl_lt (a &&& 31#64) 5 6 11 (by rw [BitVec.toNat_and]; exact Nat.and_lt_two_pow _ (by decide)) (by omega) (by omega)
  exact Nat.or_lt_two_pow (by have := h6lt b; omega) h1

theorem lo_gt (E : BitVec 64) (c : BitVec 32) (hE : E.toNat < 2 ^ 31) (hc : c.toNat < 2 ^ 31)
    (h : ¬((addSub (BitVec.setWidth 32 E) c true).snd.n == (addSub (BitVec.setWidth 32 E) c true).snd.v &&
      !decide ((BitVec.setWidth 32 E).toNat = c.toNat)) = false) : c.toNat < E.toNat := by
  have := gt32 (BitVec.setWidth 32 E) c (by rw [BitVec.toNat_setWidth]; omega) hc h
  rw [BitVec.toNat_setWidth] at this
  omega

theorem lo4 (X : BitVec 64) (hX : X.toNat < 2 ^ 21)
    (h : ¬(decide (1048575 ≤ (BitVec.setWidth 32 (X - 65536#64)).toNat) &&
      !decide ((BitVec.setWidth 32 (X - 65536#64)).toNat = 1048575)) = true) : 65536 ≤ X.toNat := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
  by_cases hl : 65536 ≤ X.toNat
  · exact hl
  · exfalso
    apply h
    have h1 : (18446744073709551616 - 65536 + X.toNat) % 18446744073709551616 % 4294967296 = X.toNat + 4294967296 - 65536 := by
      omega
    rw [h1, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
    exact ⟨by omega, by omega⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 10000 in
theorem decoderune_sum (impl : List Segment) (p len k : BitVec 64) :
    Summary (Fv256.Arm64.SfdProg.program.link impl) dr (DecPre p len k) DecPost := by
  intro s hpc ⟨hl1, hl2, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, h0, h1, h2, hacc, h48, hk, hdisj⟩
  have hm := mask_keep' len k hk (by omega)
  subst h0 h1 h2
  have h4 := rune4_lt (BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 0) + BitVec.toNat (s.regs 2)) 1))
    (BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 0) + BitVec.toNat (s.regs 2) + 1) 1))
    (BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 0) + BitVec.toNat (s.regs 2) + 2) 1))
    (BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 0) + BitVec.toNat (s.regs 2) + 3) 1))
  have h3 := rune3_lt (BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 0) + BitVec.toNat (s.regs 2)) 1))
    (BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 0) + BitVec.toNat (s.regs 2) + 1) 1))
    (BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 0) + BitVec.toNat (s.regs 2) + 2) 1))
  have h2 := rune2_lt (BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 0) + BitVec.toNat (s.regs 2)) 1))
    (BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 0) + BitVec.toNat (s.regs 2) + 1) 1))
  janus_run [hm]
  all_goals (unfold DecPost)
  all_goals (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals first | janus_frame | (simp [setReg_apply]; done) | skip
  all_goals (simp only [setReg_apply, reduceIte, Nat.reduceEqDiff])
  all_goals first
    | exact Nat.lt_trans h4 (by decide)
    | exact Nat.lt_trans h3 (by decide)
    | exact Nat.lt_trans h2 (by decide)
    | exact Nat.le_trans (by decide) (lo4 _ h4 (by janus_assumption))
    | exact Nat.le_trans (by decide : 128 ≤ 2048) (lo_gt _ 2047#32 (Nat.lt_trans h3 (by decide)) (by decide) (by janus_assumption))
    | exact Nat.le_trans (by decide : 128 ≤ 128) (lo_gt _ 127#32 (Nat.lt_trans h2 (by decide)) (by decide) (by janus_assumption))
