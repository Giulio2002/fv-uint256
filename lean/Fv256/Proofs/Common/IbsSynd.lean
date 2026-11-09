import Janus
import Fv256.Proofs.Common.IbsMath
import Fv256.Proofs.Common.IbsVec64

/-! Syndrome (two bits per byte) calculus for the arm64 `IndexByteString`: head / tail masks and windows. -/

namespace Fv256.IndexByte64
open Janus Janus.Tactic Janus.Arm64

/-- the window predicate `lo <= i < hi` -/
def wf (lo hi : Nat) (f : Nat → Bool) : Nat → Bool := fun i => decide (lo ≤ i ∧ i < hi) && f i

theorem synd_split (f : Nat → Bool) (a b : Nat) :
    synd f (a + b) = synd f a + 4 ^ a * synd (fun i => f (a + i)) b := by
  induction a generalizing f with
  | zero => simp [synd]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [synd]
    rw [ih (fun i => f (i + 1))]
    simp only [Nat.pow_succ, show ∀ i, a + 1 + i = (a + i) + 1 from fun i => by omega]
    have : ∀ i, (fun i => f (i + 1)) (a + i) = f (a + 1 + i) := fun i => by simp only []; congr 1; omega
    simp only [this]
    generalize synd (fun i => f (a + 1 + i)) b = z
    have : 4 ^ a * 4 * z = 4 * (4 ^ a * z) := by rw [Nat.mul_comm (4 ^ a) 4, Nat.mul_assoc]
    rw [this, Nat.mul_add]
    omega

theorem synd_congr {f g : Nat → Bool} {n : Nat} (h : ∀ i < n, f i = g i) : synd f n = synd g n := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [synd, h 0 (by omega)]
    rw [ih (fun i hi => h (i + 1) (by omega))]

/-- the low `e` pairs of bits -/
theorem synd_mod (f : Nat → Bool) (e : Nat) (he : e ≤ 32) :
    synd f 32 % 4 ^ e = synd f e := by
  have h := synd_split f e (32 - e)
  rw [show e + (32 - e) = 32 by omega] at h
  rw [h]
  have := synd_lt f e
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt this

theorem synd_head (f : Nat → Bool) (lo : Nat) (hlo : lo ≤ 32) :
    synd f 32 / 4 ^ lo * 4 ^ lo = synd (wf lo 32 f) 32 := by
  have h := synd_split f lo (32 - lo)
  rw [show lo + (32 - lo) = 32 by omega] at h
  have h2 := synd_split (wf lo 32 f) lo (32 - lo)
  rw [show lo + (32 - lo) = 32 by omega] at h2
  have z : synd (wf lo 32 f) lo = 0 := synd_eq_zero _ _ (fun i hi => by simp [wf]; omega)
  have e : synd (fun i => wf lo 32 f (lo + i)) (32 - lo) = synd (fun i => f (lo + i)) (32 - lo) :=
    synd_congr (fun i hi => by simp [wf]; omega)
  rw [h2, z, e, h]
  have := synd_lt f lo
  have hp : 0 < 4 ^ lo := Nat.pow_pos (by decide)
  rw [Nat.add_comm (synd f lo), Nat.mul_add_div hp, Nat.div_eq_of_lt this]
  simp [Nat.mul_comm]


open Fv256.IndexByte in
theorem synd_tail_wf (f : Nat → Bool) (e : Nat) (he : e ≤ 32) :
    synd f 32 % 4 ^ e = synd (wf 0 e f) 32 := by
  rw [synd_mod f e he]
  have h := synd_split (wf 0 e f) e (32 - e)
  rw [show e + (32 - e) = 32 by omega] at h
  rw [h]
  have z : synd (fun i => wf 0 e f (e + i)) (32 - e) = 0 := synd_eq_zero _ _ (fun i hi => by simp [wf]; omega)
  rw [z, Nat.mul_zero, Nat.add_zero]
  exact synd_congr (fun i hi => by simp [wf]; omega)

theorem wf_wf (lo e : Nat) (f : Nat → Bool) (he : e ≤ 32) (i : Nat) (hi : i < 32) :
    wf 0 e (wf lo 32 f) i = wf lo e f i := by
  simp only [wf]
  by_cases h1 : lo ≤ i <;> by_cases h2 : i < e <;> simp [h1, h2] <;> omega

/-- head then tail mask -/
theorem synd_head_tail (f : Nat → Bool) (lo e : Nat) (hlo : lo ≤ 32) (he : e ≤ 32) :
    (synd f 32 / 4 ^ lo * 4 ^ lo) % 4 ^ e = synd (wf lo e f) 32 := by
  rw [synd_head f lo hlo, synd_tail_wf _ e he]
  exact synd_congr (fun i hi => wf_wf lo e f he i hi)

/-- the tail shift of the code: `LSL` then `LSR` by `sh` (with `sh <= 64`) -/
theorem tail_shift (S sh : Nat) (hS : S < 2 ^ 64) (hsh : sh ≤ 64) :
    (S * 2 ^ sh % 2 ^ 64) / 2 ^ sh = S % 2 ^ (64 - sh) := by
  have h : 2 ^ 64 = 2 ^ sh * 2 ^ (64 - sh) := by rw [← Nat.pow_add]; congr 1; omega
  rw [h, Nat.mul_comm S, Nat.mul_mod_mul_left, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]

/-- the head shift of the code: `LSR` then `LSL` by `sh` -/
theorem head_shift (S sh : Nat) (hS : S < 2 ^ 64) (hsh : sh < 64) :
    (S / 2 ^ sh * 2 ^ sh) % 2 ^ 64 = S / 2 ^ sh * 2 ^ sh := by
  apply Nat.mod_eq_of_lt
  calc S / 2 ^ sh * 2 ^ sh ≤ S := Nat.div_mul_le_self _ _
    _ < 2 ^ 64 := hS

open Fv256.IndexByte in
theorem win_ft (f : Nat → Bool) (lo hi : Nat) (h1 : lo ≤ hi) (h2 : hi ≤ 32) :
    (firstTrue (wf lo hi f) 32 < 32 ↔ firstTrue (fun i => f (lo + i)) (hi - lo) < hi - lo) ∧
    (firstTrue (fun i => f (lo + i)) (hi - lo) < hi - lo →
      firstTrue (wf lo hi f) 32 = lo + firstTrue (fun i => f (lo + i)) (hi - lo)) := by
  have hlo : firstTrue (wf lo hi f) lo = lo := by
    rw [ft_eq_iff]; intro i hi'; simp [wf]; omega
  have e1 := ft_shift (wf lo hi f) lo (32 - lo) hlo
  rw [show lo + (32 - lo) = 32 by omega] at e1
  have e2 := ft_add' (fun i => wf lo hi f (lo + i)) (hi - lo) (32 - hi)
  rw [show hi - lo + (32 - hi) = 32 - lo by omega] at e2
  have e3 : firstTrue (fun i => wf lo hi f (lo + i)) (hi - lo) = firstTrue (fun i => f (lo + i)) (hi - lo) :=
    ft_congr (fun i hi' => by simp [wf]; omega)
  have e4 : firstTrue (fun i => (fun i => wf lo hi f (lo + i)) (hi - lo + i)) (32 - hi) = 32 - hi := by
    rw [ft_eq_iff]; intro i hi'; simp [wf]; omega
  rw [e4, e3] at e2
  rw [e1, e2]
  have := ft_le (fun i => f (lo + i)) (hi - lo)
  by_cases h : firstTrue (fun i => f (lo + i)) (hi - lo) < hi - lo
  · rw [if_pos h]; exact ⟨by omega, fun _ => rfl⟩
  · rw [if_neg h]; exact ⟨by omega, fun h' => absurd h' h⟩


/-! ## the block predicate and the results -/

open Fv256.IndexByte in
/-- the byte predicate of the block at `b` -/
def bp (m : Janus.Arm64.Memory) (b c : Nat) : Nat → Bool := fun i => decide (m.readLE (b + i) 1 = c % 256)

open Fv256.IndexByte in
theorem bp_ft (m : Janus.Arm64.Memory) (b c k : Nat) : firstTrue (bp m b c) k = FT m b c k := rfl

theorem synd_ne_exists (f : Nat → Bool) (n : Nat) (h : synd f n ≠ 0) : ∃ i < n, f i = true :=
  Classical.byContradiction fun hc => h (synd_eq_zero f n (fun i hi => by
    cases hf : f i
    · rfl
    · exact absurd ⟨i, hi, hf⟩ hc))

open Fv256.IndexByte in
theorem found_full (m : Janus.Arm64.Memory) (P d N c S : Nat) (hft : FT m P c d = d) (hr : d + 32 ≤ N)
    (hS : S = synd (bp m (P + d) c) 32) (hne : S ≠ 0) :
    ctzN 64 S = 2 * FT m (P + d) c 32 ∧ FT m (P + d) c 32 < 32 ∧ FT m P c N = d + FT m (P + d) c 32 := by
  rw [hS] at hne ⊢
  have he := synd_ne_exists _ _ hne
  have hlt : FT m (P + d) c 32 < 32 := by
    show firstTrue (bp m (P + d) c) 32 < 32
    exact (ft_lt_iff _ _).2 (by obtain ⟨i, hi, h⟩ := he; exact ⟨i, hi, h⟩)
  refine ⟨?_, hlt, FT_found m P c d N 32 hft hr hlt⟩
  rw [ctzN_synd _ 32 64 (by omega) he]; rfl

open Fv256.IndexByte in
theorem none_full (m : Janus.Arm64.Memory) (P d N c S : Nat) (hft : FT m P c d = d) (hr : N = d + 32)
    (hS : S = synd (bp m (P + d) c) 32) (hz : S = 0) : FT m P c N = N := by
  rw [hS] at hz
  have h0 : FT m (P + d) c 32 = 32 := by
    show firstTrue (bp m (P + d) c) 32 = 32
    rw [ft_eq_iff]; intro i hi
    by_cases hb : bp m (P + d) c i = true
    · exact absurd hz (synd_ne_zero _ _ ⟨i, hi, hb⟩)
    · simpa using hb
  have := FT_clean m P c d 32 hft h0
  rw [hr]; exact this

open Fv256.IndexByte in
theorem found_tail (m : Janus.Arm64.Memory) (P d N c r M : Nat) (hft : FT m P c d = d) (hr : N = d + r) (hr1 : r ≤ 32)
    (hM : M = synd (wf 0 r (bp m (P + d) c)) 32) (hne : M ≠ 0) :
    ctzN 64 M = 2 * FT m (P + d) c r ∧ FT m (P + d) c r < r ∧ FT m P c N = d + FT m (P + d) c r := by
  rw [hM] at hne ⊢
  have he := synd_ne_exists _ _ hne
  have hw := win_ft (bp m (P + d) c) 0 r (by omega) hr1
  simp only [Nat.zero_add, Nat.sub_zero] at hw
  have hlt32 : firstTrue (wf 0 r (bp m (P + d) c)) 32 < 32 := (ft_lt_iff _ _).2 he
  have hlt : FT m (P + d) c r < r := by
    show firstTrue (bp m (P + d) c) r < r
    exact hw.1.1 hlt32
  refine ⟨?_, hlt, ?_⟩
  · rw [ctzN_synd _ 32 64 (by omega) he, hw.2 hlt]; rfl
  · rw [hr]; exact FT_found m P c d (d + r) r hft (by omega) hlt

open Fv256.IndexByte in
theorem none_tail (m : Janus.Arm64.Memory) (P d N c r M : Nat) (hft : FT m P c d = d) (hr : N = d + r) (hr1 : r ≤ 32)
    (hM : M = synd (wf 0 r (bp m (P + d) c)) 32) (hz : M = 0) : FT m P c N = N := by
  rw [hM] at hz
  have h0 : FT m (P + d) c r = r := by
    show firstTrue (bp m (P + d) c) r = r
    have hw := win_ft (bp m (P + d) c) 0 r (by omega) hr1
    simp only [Nat.zero_add, Nat.sub_zero] at hw
    have hnl : ¬ firstTrue (wf 0 r (bp m (P + d) c)) 32 < 32 := by
      intro h
      have := (ft_lt_iff _ _).1 h
      exact synd_ne_zero _ _ this hz
    have := ft_le (bp m (P + d) c) r
    by_cases h : firstTrue (bp m (P + d) c) r < r
    · exact absurd (hw.1.2 h) hnl
    · omega
  have := FT_clean m P c d r hft h0
  rw [hr]; exact this


theorem synd_blk_bp (m : Janus.Arm64.Memory) (a b c0 c : Nat) (hb : b = a + 16) (hc : c0 % 256 = c % 256) :
    synd (blk (m.readLE a 16) (m.readLE b 16) c0) 32 = synd (bp m a c) 32 := by
  apply synd_congr
  intro i hi
  rw [blk_readLE m c0 hb hi]
  simp only [bp, hc]

theorem blk_none_iff (m : Janus.Arm64.Memory) (a b c0 c : Nat) (hb : b = a + 16) (hc : c0 % 256 = c % 256) :
    (∀ i < 32, blk (m.readLE a 16) (m.readLE b 16) c0 i = false) ↔ (∀ i < 32, bp m a c i = false) := by
  constructor
  · intro h i hi
    have := h i hi
    rw [blk_readLE m c0 hb hi] at this
    simpa [bp, hc] using this
  · intro h i hi
    have := h i hi
    rw [blk_readLE m c0 hb hi]
    simpa [bp, hc] using this

theorem rbit_mod' (x : Nat) : rbitNat 64 x % 18446744073709551616 = rbitNat 64 x :=
  Nat.mod_eq_of_lt (rbitNat_lt 64 x)

/-- the tail shift as the stepper presents it -/
theorem tail_eval (S k : Nat) (hS : S < 2 ^ 64) (hk1 : 1 ≤ k) (hk2 : k ≤ 31) :
    (BitVec.ofNat 64 (S * 2 ^ ((18446744073709551616 - 2 * (18446744073709551584 + k) % 18446744073709551616) % 64)) >>>
      ((18446744073709551616 - 2 * (18446744073709551584 + k) % 18446744073709551616) % 64)).toNat = S % 4 ^ k := by
  have hsh : (18446744073709551616 - 2 * (18446744073709551584 + k) % 18446744073709551616) % 64 = 64 - 2 * k := by omega
  rw [hsh, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, tail_shift S (64 - 2 * k) hS (by omega)]
  rw [show 64 - (64 - 2 * k) = 2 * k by omega, Nat.pow_mul]

/-- the result register of a found match -/
theorem x0_found (p : BitVec 64) (d Y k : Nat) (hk : ctzN 64 Y = 2 * k) (hk32 : k < 32) (hd : d + 64 < 2 ^ 63) :
    (p + BitVec.ofNat 64 (d + 32) - 32#64 + BitVec.ofNat 64 (clzNat 64 (rbitNat 64 Y % 18446744073709551616)) >>> 1 - p).toNat = d + k := by
  rw [rbit_mod', clzNat_rbitNat, hk]
  have := p.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow, Nat.reduceSub]
  omega


/-! ## the head block -/

theorem rotA (x : Nat) :
    ((((BitVec.ofNat 64 (x % 32)).rotateRight 63).toNat &&& 18446744073709551614) % 18446744073709551616 % 64) = 2 * (x % 32) := by
  have h : ∀ o < 32, ((((BitVec.ofNat 64 o).rotateRight 63).toNat &&& 18446744073709551614) % 18446744073709551616 % 64) = 2 * o := by
    decide
  exact h _ (Nat.mod_lt _ (by decide))

theorem shB (m : Nat) : (18446744073709551616 - 2 * (18446744073709551584 + m % 32) % 18446744073709551616) % 64 =
    (64 - 2 * (m % 32)) % 64 := by omega

theorem ht_eval2 (S o : Nat) (hS : S < 2 ^ 64) (ho : o < 32) :
    2 ^ (2 * o) * (BitVec.ofNat 64 S >>> (2 * o)).toNat % 18446744073709551616 = S / 4 ^ o * 4 ^ o := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hS,
    Nat.pow_mul, show (2 : Nat) ^ 2 = 4 from rfl, Nat.mul_comm]
  apply Nat.mod_eq_of_lt
  calc S / 4 ^ o * 4 ^ o ≤ S := Nat.div_mul_le_self _ _
    _ < 18446744073709551616 := hS

theorem ht_eval1 (S o k0 : Nat) (hS : S < 2 ^ 64) (ho : o < 32) (hk0 : k0 < 32) :
    (BitVec.ofNat 64 S >>> (2 * o) <<< (2 * o) <<< ((64 - 2 * k0) % 64) >>> ((64 - 2 * k0) % 64)).toNat =
      (S / 4 ^ o * 4 ^ o) % 4 ^ (if k0 = 0 then 32 else k0) := by
  have hh : S / 4 ^ o * 4 ^ o < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hS
  have e1 : (BitVec.ofNat 64 S >>> (2 * o) <<< (2 * o)).toNat = S / 4 ^ o * 4 ^ o := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt hS, Nat.pow_mul, show (2 : Nat) ^ 2 = 4 from rfl]
    exact Nat.mod_eq_of_lt hh
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, e1, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  by_cases hk : k0 = 0
  · subst hk
    simp only [Nat.mul_zero, Nat.sub_zero, Nat.reduceMod, Nat.pow_zero, Nat.mul_one, Nat.div_one, if_true]
  · rw [if_neg hk]
    have hs : (64 - 2 * k0) % 64 = 64 - 2 * k0 := Nat.mod_eq_of_lt (by omega)
    rw [hs, tail_shift _ _ hh (by omega), show 64 - (64 - 2 * k0) = 2 * k0 by omega, Nat.pow_mul]

theorem win_found (f : Nat → Bool) (lo hi M : Nat) (h1 : lo ≤ hi) (h2 : hi ≤ 32) (hM : M = synd (wf lo hi f) 32)
    (hne : M ≠ 0) :
    ctzN 64 M = 2 * (lo + firstTrue (fun i => f (lo + i)) (hi - lo)) ∧ firstTrue (fun i => f (lo + i)) (hi - lo) < hi - lo := by
  rw [hM] at hne ⊢
  have he := synd_ne_exists _ _ hne
  have hw := win_ft f lo hi h1 h2
  have hlt32 : firstTrue (wf lo hi f) 32 < 32 := (Fv256.IndexByte.ft_lt_iff _ _).2 he
  have hlt := hw.1.1 hlt32
  refine ⟨?_, hlt⟩
  rw [ctzN_synd _ 32 64 (by omega) he, hw.2 hlt]

theorem win_none (f : Nat → Bool) (lo hi M : Nat) (h1 : lo ≤ hi) (h2 : hi ≤ 32) (hM : M = synd (wf lo hi f) 32)
    (hz : M = 0) : firstTrue (fun i => f (lo + i)) (hi - lo) = hi - lo := by
  rw [hM] at hz
  have hw := win_ft f lo hi h1 h2
  have hnl : ¬ firstTrue (wf lo hi f) 32 < 32 := by
    intro h
    exact synd_ne_zero _ _ ((Fv256.IndexByte.ft_lt_iff _ _).1 h) hz
  have := Fv256.IndexByte.ft_le (fun i => f (lo + i)) (hi - lo)
  by_cases h : firstTrue (fun i => f (lo + i)) (hi - lo) < hi - lo
  · exact absurd (hw.1.2 h) hnl
  · omega

open Fv256.IndexByte in
theorem FT_bp (m : Janus.Arm64.Memory) (P a o c k : Nat) (hP : P = a + o) :
    FT m P c k = firstTrue (fun i => bp m a c (o + i)) k := by
  subst hP
  unfold FT bp
  apply ft_congr
  intro i hi
  rw [Nat.add_assoc]

/-- the result register of a match found in the head block at `a` -/
theorem x0_head (p : BitVec 64) (a o Y k : Nat) (hp : p.toNat = a + o) (hk : ctzN 64 Y = 2 * (o + k)) (hk32 : o + k < 32)
    (ha : a + 64 < 2 ^ 63) :
    (BitVec.ofNat 64 a + 32#64 - 32#64 + BitVec.ofNat 64 (clzNat 64 (rbitNat 64 Y % 18446744073709551616)) >>> 1 - p).toNat = k := by
  rw [rbit_mod', clzNat_rbitNat, hk]
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow, Nat.reduceSub]
  omega

end Fv256.IndexByte64
