import Janus
import Fv256.Proofs.Common.IndexByteSpec

/-!
Extracted-free lemmas for the `IndexByteString` summaries: first-match (`firstTrue`) calculus, the vector
compare / movemask / bit-scan facts over `BitVec`/`Nat`, and `indexOfNat`.
-/

namespace Fv256.IndexByte
open Janus Janus.Amd64 Janus.Tactic

/-- the bytes of the string at `p` as a Bool predicate: `b i = c` -/
def FT (m : Janus.Arm64.Memory) (p c : Nat) (k : Nat) : Nat :=
  firstTrue (fun i => decide (m.readLE (p + i) 1 = c % 256)) k

theorem ft_le (f : Nat → Bool) (n : Nat) : firstTrue f n ≤ n := by
  induction n generalizing f with
  | zero => simp [firstTrue]
  | succ n ih =>
    simp only [firstTrue]; split
    · omega
    · exact Nat.succ_le_succ (ih _)

theorem ft_lt_iff (f : Nat → Bool) (n : Nat) : firstTrue f n < n ↔ ∃ i < n, f i = true := by
  induction n generalizing f with
  | zero => simp [firstTrue]
  | succ n ih =>
    simp only [firstTrue]
    cases h0 : f 0
    · simp only [Bool.false_eq_true, ite_false]
      rw [show (firstTrue (fun i => f (i + 1)) n + 1 < n + 1) ↔ firstTrue (fun i => f (i + 1)) n < n by omega, ih]
      constructor
      · rintro ⟨i, hi, h⟩; exact ⟨i + 1, by omega, h⟩
      · rintro ⟨i, hi, h⟩
        cases i with
        | zero => simp [h0] at h
        | succ i => exact ⟨i, by omega, h⟩
    · simp only [ite_true]; exact ⟨fun _ => ⟨0, by omega, h0⟩, fun _ => by omega⟩

theorem ft_congr {f g : Nat → Bool} {n : Nat} (h : ∀ i < n, f i = g i) : firstTrue f n = firstTrue g n := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [firstTrue, h 0 (by omega)]
    rw [ih (fun i hi => h (i + 1) (by omega))]

/-- `firstTrue f n = n` iff no index below `n` satisfies `f` -/
theorem ft_eq_iff (f : Nat → Bool) (n : Nat) : firstTrue f n = n ↔ ∀ i < n, f i = false := by
  have h1 := ft_lt_iff f n
  have h2 := ft_le f n
  constructor
  · intro h i hi
    cases hf : f i
    · rfl
    · have := h1.2 ⟨i, hi, hf⟩
      omega
  · intro h
    by_cases hlt : firstTrue f n < n
    · obtain ⟨i, hi, he⟩ := h1.1 hlt
      rw [h i hi] at he; cases he
    · omega

theorem ft_add' (f : Nat → Bool) (a b : Nat) :
    firstTrue f (a + b) = if firstTrue f a < a then firstTrue f a else a + firstTrue (fun i => f (a + i)) b := by
  rw [firstTrue_add]
  have := ft_lt_iff f a
  by_cases h : ∃ i < a, f i = true
  · have h' : firstTrue f a < a := this.2 h
    simp [h, h']
  · have h' : ¬ firstTrue f a < a := fun hh => h (this.1 hh)
    simp [h, h']

theorem ft_prefix (f : Nat → Bool) (a b : Nat) (h : firstTrue f a < a) : firstTrue f (a + b) = firstTrue f a := by
  rw [ft_add']; simp [h]

theorem ft_shift (f : Nat → Bool) (a b : Nat) (h : firstTrue f a = a) :
    firstTrue f (a + b) = a + firstTrue (fun i => f (a + i)) b := by
  rw [ft_add']; simp [h]

/-! ## `indexOfNat` -/

theorem find_ft (b : Nat → Nat) (v n : Nat) :
    (List.range n).find? (fun i => b i == v) =
      if firstTrue (fun i => decide (b i = v)) n < n then some (firstTrue (fun i => decide (b i = v)) n) else none := by
  induction n generalizing b with
  | zero => simp [firstTrue]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.find?_cons]
    simp only [firstTrue]
    by_cases h0 : b 0 = v
    · simp [h0]
    · have h0' : (b 0 == v) = false := by simpa using h0
      rw [h0', List.find?_map]
      have : ((fun i => b i == v) ∘ Nat.succ) = (fun i => b (i + 1) == v) := by funext i; rfl
      rw [this, ih]
      simp [h0]

theorem indexOfNat_ft (b : Nat → Nat) (n c : Nat) :
    indexOfNat b n c = if firstTrue (fun i => decide (b i = c % 256)) n < n
      then firstTrue (fun i => decide (b i = c % 256)) n else 2 ^ 64 - 1 := by
  unfold indexOfNat
  rw [find_ft]
  by_cases h : firstTrue (fun i => decide (b i = c % 256)) n < n
  · simp [h]
  · simp [h]


/-! ## vector compare / movemask / bit-scan -/

theorem cmpeqBytes_lt (k a b : Nat) : cmpeqBytes k a b < 256 ^ k := by
  induction k generalizing a b with
  | zero => simp [cmpeqBytes]
  | succ k ih =>
    unfold cmpeqBytes; rw [Nat.pow_succ]
    have := ih (a / 256) (b / 256)
    split <;> omega

theorem replBytes_lt (k b : Nat) (hb : b < 256) : replBytes k b < 256 ^ k := by
  induction k with
  | zero => simp [replBytes]
  | succ k ih => unfold replBytes; rw [Nat.pow_succ]; omega

theorem msbBytes_lt' (k a : Nat) : msbBytes k a < 2 ^ k := by
  induction k generalizing a with
  | zero => simp [msbBytes]
  | succ k ih =>
    unfold msbBytes; rw [Nat.pow_succ]
    have := ih (a / 256)
    omega

theorem ctz_ft (k z : Nat) : ctzNat k z = firstTrue (fun i => decide (z / 2 ^ i % 2 = 1)) k := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    unfold ctzNat; simp only [firstTrue, Nat.pow_zero, Nat.div_one]
    by_cases h : z % 2 = 1
    · simp [h]
    · simp only [h, ite_false, decide_false, Bool.false_eq_true]
      rw [ih (z / 2), Nat.add_comm]
      congr 1
      congr 1
      funext i
      rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]

theorem mb_succ (k c a : Nat) (hc : c < 256) :
    msbBytes (k + 1) (cmpeqBytes (k + 1) a (replBytes (k + 1) c)) =
      (if a % 256 = c then 1 else 0) + 2 * msbBytes k (cmpeqBytes k (a / 256) (replBytes k c)) := by
  have hl := cmpeqBytes_lt k (a / 256) (replBytes k c)
  have hr := replBytes_lt k c hc
  have r1 : replBytes (k + 1) c = c + 256 * replBytes k c := rfl
  have r2 : cmpeqBytes (k + 1) a (c + 256 * replBytes k c) =
      (if a % 256 = (c + 256 * replBytes k c) % 256 then 255 else 0) +
        256 * cmpeqBytes k (a / 256) ((c + 256 * replBytes k c) / 256) := rfl
  have r3 : ∀ x, msbBytes (k + 1) x = x % 256 / 128 + 2 * msbBytes k (x / 256) := fun x => rfl
  rw [r1, r2, r3, show (c + 256 * replBytes k c) % 256 = c by omega, show (c + 256 * replBytes k c) / 256 = replBytes k c by omega]
  by_cases h : a % 256 = c
  · simp only [h, ite_true]
    rw [show (255 + 256 * cmpeqBytes k (a / 256) (replBytes k c)) % 256 = 255 by omega,
      show (255 + 256 * cmpeqBytes k (a / 256) (replBytes k c)) / 256 = cmpeqBytes k (a / 256) (replBytes k c) by omega]
  · simp only [h, ite_false]
    rw [show (0 + 256 * cmpeqBytes k (a / 256) (replBytes k c)) % 256 = 0 by omega,
      show (0 + 256 * cmpeqBytes k (a / 256) (replBytes k c)) / 256 = cmpeqBytes k (a / 256) (replBytes k c) by omega]

/-- bit `i` of the movemask of a byte compare with a broadcast byte -/
theorem msb_bit (k a c : Nat) (hc : c < 256) (i : Nat) (hi : i < k) :
    msbBytes k (cmpeqBytes k a (replBytes k c)) / 2 ^ i % 2 = if a / 256 ^ i % 256 = c then 1 else 0 := by
  induction k generalizing a i with
  | zero => omega
  | succ k ih =>
    rw [mb_succ k c a hc]
    cases i with
    | zero =>
      simp only [Nat.pow_zero, Nat.div_one]
      by_cases h : a % 256 = c <;> simp [h] <;> omega
    | succ i =>
      have e2 : ((if a % 256 = c then 1 else 0) + 2 * msbBytes k (cmpeqBytes k (a / 256) (replBytes k c))) / 2 ^ (i + 1) =
          msbBytes k (cmpeqBytes k (a / 256) (replBytes k c)) / 2 ^ i := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ i) 2, ← Nat.div_div_eq_div_mul]
        have : ((if a % 256 = c then 1 else 0) + 2 * msbBytes k (cmpeqBytes k (a / 256) (replBytes k c))) / 2 =
            msbBytes k (cmpeqBytes k (a / 256) (replBytes k c)) := by split <;> omega
        rw [this]
      rw [e2, ih (a / 256) i (by omega)]
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ i) 256, ← Nat.div_div_eq_div_mul]

/-- the first match of a `k`-lane compare -/
theorem ctz_msb_cmpeq (k a c : Nat) (hc : c < 256) :
    ctzNat k (msbBytes k (cmpeqBytes k a (replBytes k c))) = firstTrue (fun i => decide (a / 256 ^ i % 256 = c)) k := by
  rw [ctz_ft]
  apply ft_congr
  intro i hi
  rw [msb_bit k a c hc i hi]
  by_cases h : a / 256 ^ i % 256 = c <;> simp [h]

theorem byte_eq (m : Janus.Arm64.Memory) (q k i : Nat) (h : i < k) : m.readLE q k / 256 ^ i % 256 = m.readLE (q + i) 1 := by
  rw [Janus.Arm64.Memory.readLE_div _ _ _ _ (by omega)]
  obtain ⟨j, hj⟩ : ∃ j, k - i = j + 1 := ⟨k - i - 1, by omega⟩
  rw [hj, Janus.Arm64.Memory.readLE_succ, Janus.Arm64.Memory.readLE_one]
  have := (m.bytes (q + i)).isLt
  omega

/-- the first match among `k` bytes at `q`, from the `PCMPEQB`/`PMOVMSKB`/`BSF` of a chunk -/
theorem chunk_ft (m : Janus.Arm64.Memory) (q k c : Nat) (hc : c < 256) :
    ctzNat k (msbBytes k (cmpeqBytes k (m.readLE q k) (replBytes k c))) =
      firstTrue (fun i => decide (m.readLE (q + i) 1 = c)) k := by
  rw [ctz_msb_cmpeq _ _ _ hc]
  exact ft_congr fun i hi => by rw [byte_eq m q k i hi]

theorem cmpeq_zero_iff (k a c : Nat) (hc : c < 256) :
    cmpeqBytes k a (replBytes k c) = 0 ↔ ∀ i < k, a / 256 ^ i % 256 ≠ c := by
  induction k generalizing a with
  | zero => simp [cmpeqBytes]
  | succ k ih =>
    unfold cmpeqBytes replBytes
    rw [show (c + 256 * replBytes k c) % 256 = c by omega,
      show (c + 256 * replBytes k c) / 256 = replBytes k c by omega]
    constructor
    · intro h i hi
      have h1 : a % 256 ≠ c := by intro he; simp [he] at h
      have h2 : cmpeqBytes k (a / 256) (replBytes k c) = 0 := by split at h <;> omega
      cases i with
      | zero => simpa using h1
      | succ i =>
        have := (ih (a / 256)).1 h2 i (by omega)
        rwa [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
    · intro h
      have h1 : a % 256 ≠ c := by simpa using h 0 (by omega)
      have h2 := (ih (a / 256)).2 (fun i hi => by
        have := h (i + 1) (by omega)
        rwa [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul] at this)
      simp [h1, h2]

theorem cmpeq_msb_zero (k a b : Nat) : (msbBytes k (cmpeqBytes k a b) = 0) = (cmpeqBytes k a b = 0) := by
  apply propext
  induction k generalizing a b with
  | zero => simp [msbBytes, cmpeqBytes]
  | succ k ih =>
    unfold msbBytes cmpeqBytes
    have hl := cmpeqBytes_lt k (a / 256) (b / 256)
    rw [show ((if a % 256 = b % 256 then 255 else 0) + 256 * cmpeqBytes k (a / 256) (b / 256)) % 256 =
        (if a % 256 = b % 256 then 255 else 0) by split <;> omega,
      show ((if a % 256 = b % 256 then 255 else 0) + 256 * cmpeqBytes k (a / 256) (b / 256)) / 256 =
        cmpeqBytes k (a / 256) (b / 256) by split <;> omega]
    have := ih (a / 256) (b / 256)
    split <;> omega

/-- the chunk at `q` of `k` lanes has no match iff `FT`-style: `firstTrue = k` -/
theorem chunk_none (m : Janus.Arm64.Memory) (q k c : Nat) (hc : c < 256) :
    cmpeqBytes k (m.readLE q k) (replBytes k c) = 0 ↔
      firstTrue (fun i => decide (m.readLE (q + i) 1 = c)) k = k := by
  rw [ft_eq_iff, cmpeq_zero_iff _ _ _ hc]
  constructor
  · intro h i hi
    have := h i hi
    rw [byte_eq m q k i hi] at this
    simpa using this
  · intro h i hi
    have := h i hi
    rw [byte_eq m q k i hi]
    simpa using this


/-! ## the postcondition from the final store -/

theorem post_mk (p n : BitVec 64) (c : Nat) (s s' : Janus.Amd64.State) (r : Nat)
    (hmem : s'.mem = s.mem.writeLE ((s.regs 4).toNat + 32) 8 r)
    (h4 : s'.regs 4 = s.regs 4 + 8#64) (h5 : s'.regs 5 = s.regs 5) (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (hr : r % 2 ^ 64 = indexOfNat (bytesOf s.mem p.toNat) n.toNat c) : IbsPostA p n c s s' := by
  refine ⟨?_, h4, h5, ?_, hfs, hdf⟩
  · rw [hmem, Janus.Arm64.Memory.readLE_writeLE_self]; simpa using hr
  · rw [hmem]
    exact Janus.MemFrame.of_writeLE s.mem r (r := ((s.regs 4).toNat + 32, (s.regs 4).toNat + 40)) (List.mem_singleton.2 rfl) (Nat.le_refl _) (by omega)

/-! ## the page-crossing test `TESTW $0xff0, AX` -/

theorem tb4080 (i : Nat) : Nat.testBit 4080 i = decide (4 ≤ i ∧ i < 12) := by
  by_cases h : i < 12
  · have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 := by omega
    rcases this with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
  · have : 4080 < 2 ^ i := by
      calc 4080 < 2 ^ 12 := by decide
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow this]; simp; omega

theorem and4080_mod (z : Nat) : z &&& 4080 = (z % 2 ^ 12) &&& 4080 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and, tb4080, Nat.testBit_mod_two_pow]
  by_cases hi : i < 12 <;> simp [hi]

theorem and4080_zero (z : Nat) (hz : z < 4096) : z &&& 4080 = 0 ↔ z < 16 := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hlt
    have hz0 : z ≠ 0 := by omega
    have hb := Nat.testBit_log2 hz0
    have h1 : 4 ≤ Nat.log2 z := (Nat.le_log2 hz0).2 (by omega)
    have h2 : Nat.log2 z < 12 := (Nat.log2_lt hz0).2 (by omega)
    have := congrArg (fun x => Nat.testBit x (Nat.log2 z)) h
    simp only [Nat.testBit_and, hb, tb4080, Nat.zero_testBit] at this
    simp at this; omega
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, tb4080]
    by_cases hi : i < 4
    · simp; omega
    · have : z < 2 ^ i := by
        calc z < 16 := h
          _ = 2 ^ 4 := by decide
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.testBit_lt_two_pow this]; simp

theorem and4080_zero' (z : Nat) : z &&& 4080 = 0 ↔ z % 4096 < 16 := by
  rw [and4080_mod]; exact and4080_zero _ (Nat.mod_lt _ (by decide))

theorem pg_iff (p : BitVec 64) (h : p.toNat < 2 ^ 48) :
    (BitVec.setWidth 16 (p + 16#64) &&& 4080#16 = 0#16) ↔ 4080 ≤ p.toNat % 4096 := by
  have e : (BitVec.setWidth 16 (p + 16#64) &&& 4080#16).toNat = ((p.toNat + 16) % 65536) &&& 4080 := by
    rw [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_add]
    have : (p.toNat + (16#64).toNat) % 2 ^ 64 = p.toNat + 16 := by simp; omega
    rw [this]; rfl
  constructor
  · intro h0
    have := congrArg BitVec.toNat h0
    rw [e] at this
    have h1 : (p.toNat + 16) % 65536 &&& 4080 = 0 := by simpa using this
    rw [and4080_zero'] at h1
    omega
  · intro h0
    apply BitVec.eq_of_toNat_eq
    rw [e]
    have : (p.toNat + 16) % 65536 &&& 4080 = 0 := by
      rw [and4080_zero']; omega
    simpa using this

/-! ## the SSE broadcast -/

theorem ulb_low32 (k a b : Nat) : unpackLoBytes (k + 2) a b % 4294967296 =
    a % 256 + 256 * (b % 256) + 65536 * ((a / 256) % 256 + 256 * ((b / 256) % 256)) := by
  have r1 : ∀ k a b, unpackLoBytes (k + 1) a b = a % 256 + 256 * (b % 256) + 65536 * unpackLoBytes k (a / 256) (b / 256) := fun _ _ _ => rfl
  rw [r1, r1]
  have : unpackLoBytes k (a / 256 / 256) (b / 256 / 256) ≥ 0 := Nat.zero_le _
  omega

theorem ulb_low16 (k a b : Nat) : unpackLoBytes (k + 1) a b % 65536 = a % 256 + 256 * (b % 256) := by
  have r1 : ∀ k a b, unpackLoBytes (k + 1) a b = a % 256 + 256 * (b % 256) + 65536 * unpackLoBytes k (a / 256) (b / 256) := fun _ _ _ => rfl
  rw [r1]
  omega

theorem lowbytes (v x0 : Nat) (hx : x0 < 256) (h : v % 65536 = x0 + 256 * x0) : v % 256 = x0 ∧ v / 256 % 256 = x0 := by
  constructor
  · have : v % 256 = (v % 65536) % 256 := (Nat.mod_mod_of_dvd v (by decide : 256 ∣ 65536)).symm
    rw [this, h]; omega
  · have : v / 256 % 256 = (v % (256 * 256)) / 256 := (Nat.mod_mul_right_div_self v 256 256).symm
    rw [this, show 256 * 256 = 65536 from rfl, h]; omega

/-- the `MOVQ`/`PUNPCKLBW`/`PUNPCKLBW`/`PSHUFD $0` broadcast of the low byte -/
theorem bcast16 (W x0 : Nat) (hx : x0 < 256) (hW : W % 256 = x0) :
    pshufdNat (unpackLoBytes 8 (unpackLoBytes 8 W W % 340282366920938463463374607431768211456)
      (unpackLoBytes 8 W W % 340282366920938463463374607431768211456) % 340282366920938463463374607431768211456) 0
      = replBytes 16 x0 := by
  have h1 : unpackLoBytes 8 W W % 65536 = W % 256 + 256 * (W % 256) := ulb_low16 7 W W
  have h2 : unpackLoBytes 8 (unpackLoBytes 8 W W % 340282366920938463463374607431768211456)
      (unpackLoBytes 8 W W % 340282366920938463463374607431768211456) % 4294967296 =
      (unpackLoBytes 8 W W % 340282366920938463463374607431768211456) % 256 + 256 * ((unpackLoBytes 8 W W % 340282366920938463463374607431768211456) % 256) + 65536 * (((unpackLoBytes 8 W W % 340282366920938463463374607431768211456) / 256) % 256 + 256 * (((unpackLoBytes 8 W W % 340282366920938463463374607431768211456) / 256) % 256)) :=
    ulb_low32 6 _ _
  have e : 340282366920938463463374607431768211456 = 65536 * 5192296858534827628530496329220096 := by rfl
  have h3 : unpackLoBytes 8 W W % 340282366920938463463374607431768211456 % 65536 = x0 + 256 * x0 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 65536 ∣ 340282366920938463463374607431768211456)]; omega
  have h4 : (unpackLoBytes 8 (unpackLoBytes 8 W W % 340282366920938463463374607431768211456)
      (unpackLoBytes 8 W W % 340282366920938463463374607431768211456) % 340282366920938463463374607431768211456) % 4294967296 
      = x0 + 256 * x0 + 65536 * (x0 + 256 * x0) := by
    obtain ⟨h6, h5⟩ := lowbytes _ x0 hx h3
    rw [Nat.mod_mod_of_dvd _ (by decide : 4294967296 ∣ 340282366920938463463374607431768211456)]
    rw [h2]
    omega
  unfold pshufdNat
  simp only [Nat.zero_div, Nat.pow_zero, Nat.zero_mod, Nat.mul_zero, Nat.div_one]
  rw [h4]
  simp only [replBytes]
  omega

theorem lowbyte (p : BitVec 64) (c : Nat) :
    BitVec.toNat (p &&& 18446744073709551360#64 ||| BitVec.setWidth 64 (BitVec.ofNat 8 (c % 256))) % 256 = c % 256 := by
  rw [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.or_mod_two_pow, Nat.and_mod_two_pow]
  rw [show (18446744073709551360 : Nat) % 2 ^ 64 % 2 ^ 8 = 0 by decide, Nat.and_zero, Nat.zero_or]
  simp only [BitVec.toNat_ofNat]
  omega

/-- the broadcast xmm0 of the stub, as the stepper presents it (the byte `AL := c`) -/
theorem bcast_state (r0 : BitVec 64) (c : Nat) :
    pshufdNat (unpackLoBytes 8 (unpackLoBytes 8 (BitVec.toNat (r0 &&& 18446744073709551360#64 ||| BitVec.setWidth 64 (BitVec.ofNat 8 (c % 256))) % 340282366920938463463374607431768211456)
        (BitVec.toNat (r0 &&& 18446744073709551360#64 ||| BitVec.setWidth 64 (BitVec.ofNat 8 (c % 256))) % 340282366920938463463374607431768211456) % 340282366920938463463374607431768211456)
      (unpackLoBytes 8 (BitVec.toNat (r0 &&& 18446744073709551360#64 ||| BitVec.setWidth 64 (BitVec.ofNat 8 (c % 256))) % 340282366920938463463374607431768211456)
        (BitVec.toNat (r0 &&& 18446744073709551360#64 ||| BitVec.setWidth 64 (BitVec.ofNat 8 (c % 256))) % 340282366920938463463374607431768211456) % 340282366920938463463374607431768211456) % 340282366920938463463374607431768211456) 0
    = replBytes 16 (c % 256) := by
  apply bcast16 _ _ (Nat.mod_lt _ (by decide))
  rw [Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 340282366920938463463374607431768211456)]
  exact lowbyte r0 c

/-! ## the tails and heads -/

/-- the shifted mask of the page-boundary tail: `SHLL CX, DX; SHRL $16, DX` -/
def tailX (Mk n : Nat) : Nat :=
  (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 Mk) <<< (n % 32))) >>> 16).toNat % 4294967296

theorem tailX_eq (Mk n : Nat) (hMk : Mk < 65536) (hn : n ≤ 16) : tailX Mk n = Mk / 2 ^ (16 - n) := by
  unfold tailX
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  have h1 : Mk % 2 ^ 64 % 2 ^ 32 = Mk := by
    rw [Nat.mod_eq_of_lt (by omega : Mk < 2 ^ 64), Nat.mod_eq_of_lt (by omega : Mk < 2 ^ 32)]
  have h2 : n % 32 = n := Nat.mod_eq_of_lt (by omega)
  have h3 : Mk * 2 ^ n < 2 ^ 32 := by
    calc Mk * 2 ^ n < 2 ^ 16 * 2 ^ n := Nat.mul_lt_mul_of_pos_right hMk (Nat.two_pow_pos _)
      _ ≤ 2 ^ 16 * 2 ^ 16 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hn)
      _ = 2 ^ 32 := by rfl
  rw [h1, h2, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt (by omega : Mk * 2 ^ n < 2 ^ 64),
    Nat.mod_eq_of_lt h3]
  have h4 : (2 : Nat) ^ 16 = 2 ^ n * 2 ^ (16 - n) := by rw [← Nat.pow_add]; congr 1; omega
  rw [Nat.mod_eq_of_lt (by
      have : Mk * 2 ^ n / 2 ^ 16 ≤ Mk * 2 ^ n := Nat.div_le_self _ _
      omega), h4, Nat.mul_comm Mk, Nat.mul_div_mul_left _ _ (Nat.two_pow_pos _)]

/-- the movemask of the 16 bytes at `q` against the broadcast byte -/
def mk16 (m : Janus.Arm64.Memory) (q c : Nat) : Nat :=
  msbBytes 16 (cmpeqBytes 16 (m.readLE q 16) (replBytes 16 (c % 256)))

theorem repl16_mod (x : Nat) (hx : x < 256) : replBytes 16 x % 340282366920938463463374607431768211456 = replBytes 16 x :=
  Nat.mod_eq_of_lt (by have := replBytes_lt 16 x hx; simpa using this)

theorem tail_bits (m : Janus.Arm64.Memory) (p n c : Nat) (hn1 : 1 ≤ n) (hn : n < 16) (hq : 16 ≤ p + n) (i : Nat) (hi : i < n) :
    tailX (mk16 m (p + n - 16) c) n / 2 ^ i % 2 = if m.readLE (p + i) 1 = c % 256 then 1 else 0 := by
  have hMk : mk16 m (p + n - 16) c < 65536 := by
    have := msbBytes_lt' 16 (cmpeqBytes 16 (m.readLE (p + n - 16) 16) (replBytes 16 (c % 256)))
    simpa [mk16] using this
  rw [tailX_eq _ _ hMk (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have := msb_bit 16 (m.readLE (p + n - 16) 16) (c % 256) (Nat.mod_lt _ (by decide)) (16 - n + i) (by omega)
  unfold mk16
  rw [show 16 - n + i = 16 - n + i from rfl] 
  rw [this, byte_eq m (p + n - 16) 16 (16 - n + i) (by omega), show p + n - 16 + (16 - n + i) = p + i by omega]

theorem tail_lt (m : Janus.Arm64.Memory) (p n c : Nat) (hn : n < 16) :
    tailX (mk16 m (p + n - 16) c) n < 2 ^ n := by
  have hMk : mk16 m (p + n - 16) c < 65536 := by
    have := msbBytes_lt' 16 (cmpeqBytes 16 (m.readLE (p + n - 16) 16) (replBytes 16 (c % 256)))
    simpa [mk16] using this
  rw [tailX_eq _ _ hMk (by omega), Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
  have : n + (16 - n) = 16 := by omega
  rw [this]; simpa using hMk

theorem tail_facts (m : Janus.Arm64.Memory) (p n c : Nat) (hn1 : 1 ≤ n) (hn : n < 16) (hq : 16 ≤ p + n) :
    (tailX (mk16 m (p + n - 16) c) n = 0 ↔ FT m p c n = n) ∧
    (FT m p c n < n → ctzNat 32 (tailX (mk16 m (p + n - 16) c) n) = FT m p c n) := by
  have hlt := tail_lt m p n c hn
  have hb := tail_bits m p n c hn1 hn hq
  generalize hX : tailX (mk16 m (p + n - 16) c) n = X at hlt hb ⊢
  have hbit : ∀ i < n, (X / 2 ^ i % 2 = 1 ↔ m.readLE (p + i) 1 = c % 256) := by
    intro i hi
    rw [hb i hi]; by_cases h : m.readLE (p + i) 1 = c % 256 <;> simp [h]
  have hcong : firstTrue (fun i => decide (X / 2 ^ i % 2 = 1)) n = FT m p c n := by
    unfold FT
    apply ft_congr
    intro i hi
    have := hbit i hi
    by_cases h : m.readLE (p + i) 1 = c % 256 <;> simp_all
  have hhigh : ∀ i, n ≤ i → X / 2 ^ i % 2 = 0 := by
    intro i hi
    have : X < 2 ^ i := Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) hi)
    rw [Nat.div_eq_of_lt this]
  constructor
  · constructor
    · intro h0
      subst h0
      rw [← hcong, ft_eq_iff]
      intro i hi
      have := hbit i hi
      simp only [Nat.zero_div, Nat.zero_mod] at this
      simpa using this
    · intro h
      rw [← hcong, ft_eq_iff] at h
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.zero_testBit]
      by_cases hi : i < n
      · have := h i hi
        simpa using this
      · simp [hhigh i (by omega)]
  · intro hf
    rw [ctz_ft, show 32 = n + (32 - n) by omega, ft_add', hcong]
    simp [hf]

theorem FT_add (m : Janus.Arm64.Memory) (p c a b : Nat) :
    FT m p c (a + b) = if FT m p c a < a then FT m p c a else a + FT m (p + a) c b := by
  unfold FT
  rw [ft_add']
  have : (fun i => decide (m.readLE (p + (a + i)) 1 = c % 256)) = (fun i => decide (m.readLE (p + a + i) 1 = c % 256)) := by
    funext i; rw [Nat.add_assoc]
  rw [this]

theorem FT_zero (m : Janus.Arm64.Memory) (p c : Nat) : FT m p c 0 = 0 := rfl

theorem FT_le (m : Janus.Arm64.Memory) (p c k : Nat) : FT m p c k ≤ k := ft_le _ _

theorem chunkFT (m : Janus.Arm64.Memory) (q c k : Nat) :
    ctzNat k (msbBytes k (cmpeqBytes k (m.readLE q k) (replBytes k (c % 256)))) = FT m q c k :=
  chunk_ft m q k (c % 256) (Nat.mod_lt _ (by decide))

theorem chunkNone (m : Janus.Arm64.Memory) (q c k : Nat) :
    cmpeqBytes k (m.readLE q k) (replBytes k (c % 256)) = 0 ↔ FT m q c k = k :=
  chunk_none m q k (c % 256) (Nat.mod_lt _ (by decide))

theorem ctz_ext (k j x : Nat) (hx : x < 2 ^ k) (h0 : x ≠ 0) : ctzNat (k + j) x = ctzNat k x := by
  induction k generalizing x with
  | zero => simp at hx; omega
  | succ k ih =>
    rw [show k + 1 + j = (k + j) + 1 by omega]
    unfold ctzNat
    by_cases h : x % 2 = 1
    · simp [h]
    · simp only [h, ite_false]
      have : x / 2 < 2 ^ k := by rw [Nat.pow_succ] at hx; omega
      rw [ih (x / 2) this (by omega)]

theorem msb_pos (m : Janus.Arm64.Memory) (q c k : Nat) : msbBytes k (cmpeqBytes k (m.readLE q k) (replBytes k (c % 256))) < 2 ^ k :=
  msbBytes_lt' _ _

theorem mk_zero_iff (m : Janus.Arm64.Memory) (q c k : Nat) :
    msbBytes k (cmpeqBytes k (m.readLE q k) (replBytes k (c % 256))) = 0 ↔ FT m q c k = k := by
  rw [cmpeq_msb_zero]; exact chunkNone m q c k

theorem head_facts (m : Janus.Arm64.Memory) (p n c : Nat) (hn : n ≤ 16) :
    (FT m p c 16 < n ↔ FT m p c n < n) ∧ (FT m p c 16 < n → FT m p c n = FT m p c 16) := by
  have h := FT_add m p c n (16 - n)
  rw [show n + (16 - n) = 16 by omega] at h
  have h1 := FT_le m p c n
  by_cases hf : FT m p c n < n
  · rw [if_pos hf] at h; rw [h]; exact ⟨⟨fun _ => hf, fun _ => hf⟩, fun _ => rfl⟩
  · rw [if_neg hf] at h
    exact ⟨⟨fun hh => by omega, fun hh => absurd hh hf⟩, fun hh => by omega⟩


theorem idx_FT (m : Janus.Arm64.Memory) (p n c : Nat) :
    indexOfNat (bytesOf m p) n c = if FT m p c n < n then FT m p c n else 2 ^ 64 - 1 := by
  rw [indexOfNat_ft]; rfl

theorem ctz32_mk16 (m : Janus.Arm64.Memory) (q c : Nat) (h : mk16 m q c ≠ 0) :
    ctzNat 32 (mk16 m q c) = FT m q c 16 := by
  have h1 : mk16 m q c < 2 ^ 16 := msbBytes_lt' _ _
  have := ctz_ext 16 16 (mk16 m q c) h1 h
  rw [show 32 = 16 + 16 by rfl, this]
  exact chunkFT m q c 16

theorem head_res (m : Janus.Arm64.Memory) (p n c : Nat) (hn : n < 16) :
    (mk16 m p c = 0 → indexOfNat (bytesOf m p) n c = 2 ^ 64 - 1) ∧
    (mk16 m p c ≠ 0 → ctzNat 32 (mk16 m p c) < n → indexOfNat (bytesOf m p) n c = ctzNat 32 (mk16 m p c)) ∧
    (mk16 m p c ≠ 0 → ¬ ctzNat 32 (mk16 m p c) < n → indexOfNat (bytesOf m p) n c = 2 ^ 64 - 1) := by
  have hz : mk16 m p c = 0 ↔ FT m p c 16 = 16 := mk_zero_iff m p c 16
  obtain ⟨hf1, hf2⟩ := head_facts m p n c (by omega)
  have hle := FT_le m p c n
  have hle16 := FT_le m p c 16
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have := hz.1 h0
    rw [idx_FT]
    have : ¬ FT m p c n < n := fun hh => by have := hf1.2 hh; omega
    simp [this]
  · intro h0 hlt
    rw [ctz32_mk16 m p c h0] at hlt ⊢
    rw [idx_FT, hf2 hlt]
    have := hf1.1 hlt
    simp [hlt]
  · intro h0 hlt
    rw [ctz32_mk16 m p c h0] at hlt
    rw [idx_FT]
    have : ¬ FT m p c n < n := fun hh => hlt (hf1.2 hh)
    simp [this]

theorem mk16_mod32 (m : Janus.Arm64.Memory) (q c : Nat) :
    msbBytes 16 (cmpeqBytes 16 (m.readLE q 16) (replBytes 16 (c % 256) % 340282366920938463463374607431768211456)) % 4294967296 = mk16 m q c := by
  unfold mk16
  rw [repl16_mod _ (Nat.mod_lt _ (by decide))]
  have := msbBytes_lt' 16 (cmpeqBytes 16 (m.readLE q 16) (replBytes 16 (c % 256)))
  exact Nat.mod_eq_of_lt (by omega)

theorem ctz_le (k x : Nat) : ctzNat k x ≤ k := by
  induction k generalizing x with
  | zero => simp [ctzNat]
  | succ k ih =>
    unfold ctzNat; split
    · omega
    · have := ih (x / 2); omega

theorem mk16_zero_iff (m : Janus.Arm64.Memory) (q c : Nat) : mk16 m q c = 0 ↔ FT m q c 16 = 16 :=
  mk_zero_iff m q c 16

theorem FT_prefix_eq (m : Janus.Arm64.Memory) (p c k k' : Nat) (h : FT m p c k = k) (hk : k' ≤ k) : FT m p c k' = k' := by
  unfold FT at h ⊢
  rw [ft_eq_iff] at h ⊢
  intro i hi
  exact h i (by omega)

/-- a match in the chunk `[j, j+k)` after a clean prefix is the first match of the whole string -/
theorem FT_found (m : Janus.Arm64.Memory) (p c j n k : Nat) (hft : FT m p c j = j) (hjn : j + k ≤ n)
    (hfound : FT m (p + j) c k < k) : FT m p c n = j + FT m (p + j) c k := by
  have h1 := FT_add m p c j k
  rw [hft, if_neg (Nat.lt_irrefl j)] at h1
  have h2 := FT_add m p c (j + k) (n - (j + k))
  rw [show j + k + (n - (j + k)) = n by omega, h1, if_pos (by omega)] at h2
  exact h2

theorem FT_clean (m : Janus.Arm64.Memory) (p c j k : Nat) (hft : FT m p c j = j)
    (hnone : FT m (p + j) c k = k) : FT m p c (j + k) = j + k := by
  rw [FT_add, hft, if_neg (Nat.lt_irrefl j), hnone]

/-- the tail chunk `[n-k, n)` after a clean prefix `[0, j)`, `n - k ≤ j` -/
theorem FT_tail (m : Janus.Arm64.Memory) (p c j n k : Nat) (hft : FT m p c j = j) (hn : k ≤ n) (hj : n - k ≤ j) :
    FT m p c n = if FT m (p + n - k) c k < k then n - k + FT m (p + n - k) c k else n := by
  have h0 := FT_prefix_eq m p c j (n - k) hft hj
  have h1 := FT_add m p c (n - k) k
  rw [show n - k + k = n by omega, h0, if_neg (Nat.lt_irrefl _), show p + (n - k) = p + n - k by omega] at h1
  rw [h1]
  have := FT_le m (p + n - k) c k
  by_cases h : FT m (p + n - k) c k < k
  · simp [h]
  · have : FT m (p + n - k) c k = k := by omega
    simp [this]; omega

/-! ## the AVX2 chunk -/

theorem ymmJoin_rep (c : Nat) :
    ymmJoin (BitVec.ofNat 128 (replBytes 32 (c % 256) / 340282366920938463463374607431768211456))
      (BitVec.ofNat 128 (replBytes 32 (c % 256))) = replBytes 32 (c % 256) := by
  have h := replBytes_lt 32 (c % 256) (Nat.mod_lt _ (by decide))
  have h2 : replBytes 32 (c % 256) < 340282366920938463463374607431768211456 * 340282366920938463463374607431768211456 := by
    simpa using h
  unfold ymmJoin
  simp only [BitVec.toNat_ofNat]
  have h3 : replBytes 32 (c % 256) / 340282366920938463463374607431768211456 < 340282366920938463463374607431768211456 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]; exact h2
  rw [show (2 : Nat) ^ 128 = 340282366920938463463374607431768211456 from rfl,
    Nat.mod_eq_of_lt h3]
  have := Nat.div_add_mod (replBytes 32 (c % 256)) 340282366920938463463374607431768211456
  omega

def mk32 (m : Janus.Arm64.Memory) (q c : Nat) : Nat :=
  msbBytes 32 (cmpeqBytes 32 (m.readLE q 32) (replBytes 32 (c % 256)))

theorem mk32_zero_iff (m : Janus.Arm64.Memory) (q c : Nat) : mk32 m q c = 0 ↔ FT m q c 32 = 32 :=
  mk_zero_iff m q c 32

theorem ctz_mk32 (m : Janus.Arm64.Memory) (q c : Nat) : ctzNat 32 (mk32 m q c) = FT m q c 32 :=
  chunkFT m q c 32

theorem mk32_mod32 (m : Janus.Arm64.Memory) (q c : Nat) : mk32 m q c % 4294967296 = mk32 m q c :=
  Nat.mod_eq_of_lt (msbBytes_lt' 32 _)

theorem cmpeq32_zero_iff (m : Janus.Arm64.Memory) (q c : Nat) :
    cmpeqBytes 32 (m.readLE q 32) (replBytes 32 (c % 256)) = 0 ↔ FT m q c 32 = 32 :=
  chunkNone m q c 32

/-- signed compare of two small 64-bit values -/
theorem toInt_lt_iff (x y : BitVec 64) (hx : x.toNat < 2 ^ 63) (hy : y.toNat < 2 ^ 63) :
    x.toInt < y.toInt ↔ x.toNat < y.toNat := by
  rw [BitVec.toInt_eq_toNat_of_lt (by omega), BitVec.toInt_eq_toNat_of_lt (by omega)]
  omega

theorem toNat_add_ofNat (p : BitVec 64) (k : Nat) (h : p.toNat + k < 2 ^ 64) : (p + BitVec.ofNat 64 k).toNat = p.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : k % 2 ^ 64 = k := Nat.mod_eq_of_lt (by omega)
  rw [this]; exact Nat.mod_eq_of_lt h

theorem toNat_add_sub (p n : BitVec 64) (k : Nat) (hk : k ≤ n.toNat) (h : p.toNat + n.toNat < 2 ^ 64) :
    (p + n - BitVec.ofNat 64 k).toNat = p.toNat + n.toNat - k := by
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  have : k % 2 ^ 64 = k := Nat.mod_eq_of_lt (by omega)
  rw [this, Nat.mod_eq_of_lt h]
  omega

end Fv256.IndexByte
