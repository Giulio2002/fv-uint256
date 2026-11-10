import Janus
import Fv256.Spec.Core
import Fv256.Proofs.Legacy.FromBE
import Fv256.Spec.BigEndian
import Fv256.Spec.Bytes

/-!
# Bridge: the readable byte-list specifications (`Fv256/Spec/BigEndian.lean`) versus the number-reading form the proofs use

The proofs of the byte-output functions (`Bytes32`, `WriteToSlice`, `MarshalSSZ`, ...) were written against
`Spec.fromBE bytes n = x % 256^n` (read `n` memory bytes as a big-endian number) and `Memory.readLE a n = x` (read `n` bytes as a
little-endian number). The claims state the same facts as "the bytes ARE `Spec.beBytes n x` / `Spec.leBytes n x`".
This module proves those two statement forms equivalent, once, for every `n`, `x` and every byte function.
-/

namespace Fv256.Proofs.Bytes

open Fv256.Spec

theorem fromBE_lt : ∀ (n : Nat) (f : Nat → Nat), (∀ i < n, f i < 256) → fromBE f n < 256 ^ n
  | 0, f, _ => by simp [fromBE]
  | n + 1, f, hf => by
    have ih := fromBE_lt n (fun i => f (i + 1)) (fun i hi => hf (i + 1) (by omega))
    have h0 := hf 0 (by omega)
    simp only [fromBE, Nat.pow_succ]
    have : f 0 * 256 ^ n ≤ 255 * 256 ^ n := Nat.mul_le_mul_right _ (by omega)
    omega

/-- Reading `n` bytes big-endian gives `x mod 256^n` exactly when byte `i` is `⌊x / 256^(n-1-i)⌋ mod 256`. -/
theorem fromBE_iff : ∀ (n : Nat) (f : Nat → Nat) (x : Nat), (∀ i < n, f i < 256) →
    (fromBE f n = x % 256 ^ n ↔ ∀ i < n, f i = x / 256 ^ (n - 1 - i) % 256)
  | 0, f, x, _ => by simp [fromBE, Nat.mod_one]
  | n + 1, f, x, hf => by
    have ih := fromBE_iff n (fun i => f (i + 1)) x (fun i hi => hf (i + 1) (by omega))
    have hlt := fromBE_lt n (fun i => f (i + 1)) (fun i hi => hf (i + 1) (by omega))
    have h0 := hf 0 (by omega)
    have hp : (256 : Nat) ^ (n + 1) = 256 ^ n * 256 := Nat.pow_succ ..
    have hpos : 0 < 256 ^ n := Nat.pow_pos (by omega)
    have hmod : x % 256 ^ (n + 1) = x % 256 ^ n + 256 ^ n * (x / 256 ^ n % 256) := by
      rw [hp]; exact Nat.mod_mul
    have hxlt : x % 256 ^ n < 256 ^ n := Nat.mod_lt _ hpos
    have hx2 : x / 256 ^ n % 256 < 256 := Nat.mod_lt _ (by omega)
    have key : (f 0 * 256 ^ n + fromBE (fun i => f (i + 1)) n = x % 256 ^ (n + 1)) ↔
        (f 0 = x / 256 ^ n % 256 ∧ fromBE (fun i => f (i + 1)) n = x % 256 ^ n) := by
      rw [hmod]
      constructor
      · intro h
        have a := (Nat.div_mod_unique (b := 256 ^ n) (a := f 0 * 256 ^ n + fromBE (fun i => f (i + 1)) n)
          (d := f 0) (c := fromBE (fun i => f (i + 1)) n) hpos).2 ⟨by rw [Nat.mul_comm]; omega, hlt⟩
        have b := (Nat.div_mod_unique (b := 256 ^ n) (a := f 0 * 256 ^ n + fromBE (fun i => f (i + 1)) n)
          (d := x / 256 ^ n % 256) (c := x % 256 ^ n) hpos).2 ⟨h.symm, hxlt⟩
        omega
      · rintro ⟨h1, h2⟩; rw [h1, h2, Nat.mul_comm]; omega
    simp only [fromBE]
    rw [key, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      cases i with
      | zero => simpa using h1
      | succ j => have := h2 j (by omega); simpa [show n - (j + 1) = n - 1 - j by omega] using this
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun j hj => ?_⟩
      have := h (j + 1) (by omega); simpa [show n - (j + 1) = n - 1 - j by omega] using this

/-- BYTE LIST FORM, big-endian: the list of `n` bytes `f 0, …, f (n-1)` is `beBytes n x` iff they read big-endian as `x mod 256^n`. -/
theorem beBytes_iff (n x : Nat) (f : Nat → Nat) (hf : ∀ i < n, f i < 256) :
    (List.range n).map f = beBytes n x ↔ fromBE f n = x % 256 ^ n := by
  rw [fromBE_iff n f x hf, beBytes, List.map_inj_left]
  simp

/-- Memory form of `beBytes_iff`: the `n` bytes at `a` are `beBytes n x` iff they read (`fromBE`) as `x mod 256^n`. -/
theorem mem_beBytes_iff (m : Janus.Arm64.Memory) (a n x : Nat) :
    (List.range n).map (fun i => m.readLE (a + i) 1) = beBytes n x ↔
      fromBE (fun i => m.readLE (a + i) 1) n = x % 256 ^ n :=
  beBytes_iff n x _ fun i _ => by simpa using Janus.Arm64.Memory.readLE_lt m (a + i) 1

/-- Same as `mem_beBytes_iff` with the modulus written as `2^(8 n)` (the form the proofs use). -/
theorem mem_beBytes_iff_two (m : Janus.Arm64.Memory) (a n x : Nat) :
    (List.range n).map (fun i => m.readLE (a + i) 1) = beBytes n x ↔
      fromBE (fun i => m.readLE (a + i) 1) n = x % 2 ^ (8 * n) := by
  rw [mem_beBytes_iff, show (256 : Nat) ^ n = 2 ^ (8 * n) by rw [Nat.pow_mul]]

/-- Same as `mem_beBytes_iff` for a number `x` already below `256^n` (no reduction). -/
theorem mem_beBytes_iff' (m : Janus.Arm64.Memory) (a n x : Nat) (hx : x < 256 ^ n) :
    (List.range n).map (fun i => m.readLE (a + i) 1) = beBytes n x ↔
      fromBE (fun i => m.readLE (a + i) 1) n = x := by
  rw [mem_beBytes_iff, Nat.mod_eq_of_lt hx]

/-- Reading `n` bytes little-endian gives `x mod 256^n` exactly when byte `i` is `⌊x / 256^i⌋ mod 256`. -/
theorem readLE_iff : ∀ (n : Nat) (m : Janus.Arm64.Memory) (a x : Nat),
    (m.readLE a n = x % 256 ^ n ↔ ∀ i < n, m.readLE (a + i) 1 = x / 256 ^ i % 256)
  | 0, m, a, x => by simp [Nat.mod_one]
  | n + 1, m, a, x => by
    have ih := readLE_iff n m (a + 1) (x / 256)
    have hpos : 0 < 256 ^ n := Nat.pow_pos (by omega)
    have hp : (256 : Nat) ^ (n + 1) = 256 * 256 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    have hadd : m.readLE a (n + 1) = m.readLE a 1 + 256 ^ 1 * m.readLE (a + 1) n := by
      rw [show n + 1 = 1 + n by omega, Janus.Arm64.Memory.readLE_add]
    have hlt1 := Janus.Arm64.Memory.readLE_lt m a 1
    have hltn := Janus.Arm64.Memory.readLE_lt m (a + 1) n
    simp only [Nat.pow_one] at hadd hlt1
    have hmod : x % 256 ^ (n + 1) = x % 256 + 256 * (x / 256 % 256 ^ n) := by rw [hp]; exact Nat.mod_mul
    have key : (m.readLE a 1 + 256 * m.readLE (a + 1) n = x % 256 ^ (n + 1)) ↔
        (m.readLE a 1 = x % 256 ∧ m.readLE (a + 1) n = x / 256 % 256 ^ n) := by
      rw [hmod]
      have hx1 : x % 256 < 256 := Nat.mod_lt _ (by omega)
      have hx2 : x / 256 % 256 ^ n < 256 ^ n := Nat.mod_lt _ hpos
      constructor
      · intro h
        have a1 := (Nat.div_mod_unique (b := 256) (a := m.readLE a 1 + 256 * m.readLE (a + 1) n)
          (d := m.readLE (a + 1) n) (c := m.readLE a 1) (by omega)).2 ⟨rfl, by omega⟩
        have b1 := (Nat.div_mod_unique (b := 256) (a := m.readLE a 1 + 256 * m.readLE (a + 1) n)
          (d := x / 256 % 256 ^ n) (c := x % 256) (by omega)).2 ⟨h.symm, hx1⟩
        omega
      · rintro ⟨h1, h2⟩; rw [h1, h2]
    rw [hadd, key, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      cases i with
      | zero => simpa using h1
      | succ j =>
        have := h2 j (by omega)
        rw [show a + (j + 1) = a + 1 + j by omega, this, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (256 ^ j)]
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun j hj => ?_⟩
      have := h (j + 1) (by omega)
      rw [show a + (j + 1) = a + 1 + j by omega] at this
      rw [this, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (256 ^ j)]

/-- BYTE LIST FORM, little-endian: the `n` bytes at `a` are `leBytes n x` iff they read little-endian (`readLE`) as `x mod 256^n`. -/
theorem mem_leBytes_iff (m : Janus.Arm64.Memory) (a n x : Nat) :
    (List.range n).map (fun i => m.readLE (a + i) 1) = leBytes n x ↔ m.readLE a n = x % 256 ^ n := by
  rw [readLE_iff, leBytes, List.map_inj_left]
  simp

/-- Same as `mem_leBytes_iff` for a number `x` already below `256^n`. -/
theorem mem_leBytes_iff' (m : Janus.Arm64.Memory) (a n x : Nat) (hx : x < 256 ^ n) :
    (List.range n).map (fun i => m.readLE (a + i) 1) = leBytes n x ↔ m.readLE a n = x := by
  rw [mem_leBytes_iff, Nat.mod_eq_of_lt hx]

/-- `Spec.minBytes` (the readable byte count of `Bytes`) is the older `Spec.byteLen`. -/
theorem minBytes_eq_byteLen (x : Nat) : minBytes x = byteLen x := by
  unfold minBytes byteLen bitLen
  split <;> omega

/-- The minimal encoding has room for `x`: `x < 256^(minBytes x)`. -/
theorem lt_pow_minBytes (x : Nat) : x < 256 ^ minBytes x := by
  unfold minBytes
  split
  · omega
  · rename_i h
    have h1 : x < 2 ^ (x.log2 + 1) := Nat.lt_log2_self
    have h2 : 2 ^ (x.log2 + 1) ≤ 2 ^ (8 * (x.log2 / 8 + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.pow_mul] at h2
    simpa using Nat.lt_of_lt_of_le h1 h2


/-- A 32-byte number read little-endian from memory `m` at `b` is exactly what the 32 bytes at `a` in `m'` spell, little-endian. -/
theorem mem_leBytes_iff_rd (m m' : Janus.Arm64.Memory) (a b : Nat) :
    (List.range 32).map (fun i => m'.readLE (a + i) 1) = leBytes 32 (m.readLE b 32) ↔ m'.readLE a 32 = m.readLE b 32 :=
  mem_leBytes_iff' m' a 32 _ (Janus.Arm64.Memory.readLE_lt m b 32)

/-- The minimal encoding as memory bytes: the `minBytes x` bytes at `a` are `Spec.bytes x` iff they read big-endian (`fromBE`) as exactly `x`. -/
theorem mem_bytes_iff (m : Janus.Arm64.Memory) (a x : Nat) :
    (List.range (minBytes x)).map (fun i => m.readLE (a + i) 1) = Fv256.Spec.bytes x ↔
      fromBE (fun i => m.readLE (a + i) 1) (minBytes x) = x :=
  mem_beBytes_iff' m a (minBytes x) x (lt_pow_minBytes x)

end Fv256.Proofs.Bytes
