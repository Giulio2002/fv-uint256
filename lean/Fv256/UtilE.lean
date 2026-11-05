import Janus

/-!
# Shared lemmas for family E (own file; FV-A owns `Util.lean`)
-/

open Janus Janus.Amd64

namespace Fv256.E

/-- A writable range is disjoint from every read-only data object (`Program.DataLoaded`). -/
theorem dataLoaded_disjoint {p : Janus.Amd64.Program} {m : Janus.Arm64.Memory} (h : p.DataLoaded m) {d : Janus.DataSegment}
    (hd : d ∈ p.data) {a n : Nat} (hw : m.accessible a n true = true) :
    a + n ≤ d.base ∨ d.base + d.bytes.length ≤ a := by
  obtain ⟨hreg, _⟩ := h d hd
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hreg
  obtain ⟨r, hr, ⟨⟨⟨hb, he⟩, _⟩, hro⟩⟩ := hreg
  simp only [Janus.Arm64.Memory.accessible, Bool.and_eq_true, Bool.not_true, Bool.false_or,
    List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hw
  rcases hw.2 r hr with (h1 | h1) | h1
  · rw [hro] at h1; cases h1
  · omega
  · omega

/-- Stores to writable memory keep the program's read-only data loaded. -/
theorem dataLoaded_writeLE {p : Janus.Amd64.Program} {m : Janus.Arm64.Memory} (h : p.DataLoaded m) {a n : Nat}
    (hw : m.accessible a n true = true) (v : Nat) : p.DataLoaded (m.writeLE a n v) := by
  intro d hd
  obtain ⟨hreg, hb⟩ := h d hd
  refine ⟨by simpa using hreg, fun i hi => ?_⟩
  have hdj := dataLoaded_disjoint h hd hw
  have hdisj : d.base + i < a ∨ a + n ≤ d.base + i := by omega
  rw [Janus.Arm64.Memory.bytes_writeLE_outside (m := m) (v := v) hdisj]
  exact hb i hi

/-- Sequential composition of two `ReachesRet` runs. -/
theorem reachesRet_bind {p : Janus.Amd64.Program} {t1 t2 : Janus.Amd64.W64} {s : Janus.Amd64.State}
    {Q1 Q2 : Janus.Amd64.State → Prop} (h : Janus.Amd64.Tactic.ReachesRet p t1 s Q1)
    (h2 : ∀ s', Q1 s' → Janus.Amd64.Tactic.ReachesRet p t2 s' Q2) :
    Janus.Amd64.Tactic.ReachesRet p t2 s Q2 := by
  obtain ⟨k, s', hst, hr, hq⟩ := h
  obtain ⟨k', s'', hst', hr', hq'⟩ := h2 s' hq
  exact ⟨k + k', s'', hst.trans hst', hr', hq'⟩

/-- Subtracting a small constant from a 64-bit numeral. -/
theorem ofNat_sub_ofNat (i k : Nat) (hk : k ≤ i) (hi : i < 2 ^ 64) :
    BitVec.ofNat 64 i - BitVec.ofNat 64 k = BitVec.ofNat 64 (i - k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt (by omega : i - k < 2 ^ 64)]
  omega

/-- Subtracting a literal from a 64-bit register value. -/
theorem bv_sub_lit (x : BitVec 64) (k : Nat) (h : k ≤ x.toNat) :
    x - BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat - k) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  by_cases hk : k < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega : x.toNat - k < 2 ^ 64)]; omega
  · omega

/-- Adding a literal to a 64-bit register value. -/
theorem bv_add_lit (x : BitVec 64) (k : Nat) (h : x.toNat + k < 2 ^ 64) :
    x + BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat + k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : k < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]

theorem steps_link {p : Janus.Amd64.Program} (impl : List Janus.Amd64.Segment) {s s' : Janus.Amd64.State} {k : Nat}
    (h : Janus.Amd64.Program.Steps p s k s') : Janus.Amd64.Program.Steps (p.link impl) s k s' := by
  induction h with
  | refl => exact .refl _
  | step hx hs hf hst _ ih =>
    exact .step (by simpa using hx) (by simpa using hs) (Janus.Amd64.Program.fetch_link impl hf) hst ih

/-- A summary of `p` is a summary of `p` linked with any further code (the callee runs only its own code). -/
theorem summary_link {p : Janus.Amd64.Program} (impl : List Janus.Amd64.Segment) {entry : Nat}
    {pre : Janus.Amd64.State → Prop} {post : Janus.Amd64.State → Janus.Amd64.State → Prop}
    (h : Janus.Amd64.Tactic.Summary p entry pre post) : Janus.Amd64.Tactic.Summary (p.link impl) entry pre post := by
  intro s hpc hp
  obtain ⟨k, s', hst, hr, hq⟩ := h s hpc hp
  exact ⟨k, s', steps_link impl hst, hr, hq⟩

open Janus.Arm64 in
/-- One byte of a window read: `(M.readLE a w) / 256^j % 256 = M.readLE (a+j) 1` for `j < w`. -/
theorem readLE_byte_of_window (M : Janus.Arm64.Memory) (a w j : Nat) (hj : j < w) :
    M.readLE a w / 256 ^ j % 256 ^ 1 = M.readLE (a + j) 1 := by
  rw [Memory.readLE_div M a w j (by omega), ← Memory.readLE_mod M (a + j) (w - j) 1 (by omega)]

open Janus.Arm64 in
/-- The two overlapping stores of a small `memmove`: the first `w1` bytes and the last `w2` bytes
(`w1, w2 ≤ n ≤ w1 + w2`), the source read before either store; the ranges do not overlap. -/
theorem two_copy (M : Janus.Arm64.Memory) (d s n w1 w2 : Nat) (h1 : w1 ≤ n) (h2 : w2 ≤ n) (h3 : n ≤ w1 + w2)
    (hdisj : d + n ≤ s ∨ s + n ≤ d) :
    ∀ i, i < n → ((M.writeLE d w1 (M.readLE s w1)).writeLE (d + n - w2) w2 (M.readLE (s + n - w2) w2)).readLE (d + i) 1
      = M.readLE (s + i) 1 := by
  intro i hi
  by_cases hc : n - w2 ≤ i
  · rw [Memory.readLE_writeLE_inside _ _ (by omega) (by omega), show d + i - (d + n - w2) = i - (n - w2) by omega,
      readLE_byte_of_window M (s + n - w2) w2 (i - (n - w2)) (by omega)]
    congr 1; omega
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_inside _ _ (by omega) (by omega),
      show d + i - d = i by omega, readLE_byte_of_window M s w1 i (by omega)]

/-- A zero-extended `w`-bit register image of a memory read, stored back, is the read itself. -/
theorem zx_store (k v : Nat) (hv : v < 2 ^ k) (hk : k ≤ 64) :
    BitVec.toNat (0#64 ||| BitVec.setWidth 64 (BitVec.ofNat k v)) % 2 ^ k = v := by
  have h1 : (BitVec.setWidth 64 (BitVec.ofNat k v)).toNat = v := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) hk))
  have h2 : (0#64 ||| BitVec.setWidth 64 (BitVec.ofNat k v)) = BitVec.setWidth 64 (BitVec.ofNat k v) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_or, h1]; simp
  rw [h2, h1, Nat.mod_eq_of_lt hv]

theorem two_copy' (M : Janus.Arm64.Memory) (d s n w1 w2 : Nat) (h1 : w1 ≤ n) (h2 : w2 ≤ n) (h3 : n ≤ w1 + w2)
    (hdisj : d + n ≤ s ∨ s + n ≤ d) :
    ∀ i, i < n → ((M.writeLE d w1 (M.readLE s w1)).writeLE (d + (n - w2)) w2 (M.readLE (s + (n - w2)) w2)).readLE (d + i) 1
      = M.readLE (s + i) 1 := by
  intro i hi
  have := two_copy M d s n w1 w2 h1 h2 h3 hdisj i hi
  rwa [show d + n - w2 = d + (n - w2) by omega, show s + n - w2 = s + (n - w2) by omega] at this

/-- Two stores inside one writable buffer keep the read-only data. -/
theorem dataLoaded_two {p : Janus.Amd64.Program} {m : Janus.Arm64.Memory} (h : p.DataLoaded m) {b n : Nat}
    (hb : m.accessible b n true = true) {a1 k1 a2 k2 : Nat} (h1 : b ≤ a1) (h2 : a1 + k1 ≤ b + n)
    (h3 : b ≤ a2) (h4 : a2 + k2 ≤ b + n) (v1 v2 : Nat) :
    p.DataLoaded ((m.writeLE a1 k1 v1).writeLE a2 k2 v2) := by
  refine dataLoaded_writeLE (dataLoaded_writeLE h (Janus.Amd64.Tactic.accessible_sub hb (Or.inr rfl) h1 h2) _) ?_ _
  simp only [Janus.Arm64.Memory.accessible_writeLE]
  exact Janus.Amd64.Tactic.accessible_sub hb (Or.inr rfl) h3 h4

/-- Storing the low 16 bits of `AX` after `MOVW (mem), AX` (the upper 48 bits keep the old value). -/
theorem merge_store16 (x : BitVec 64) (v : Nat) (hv : v < 65536) :
    BitVec.toNat (x &&& 18446744073709486080#64 ||| BitVec.setWidth 64 (BitVec.ofNat 16 v)) % 65536 = v := by
  have h1 : (BitVec.setWidth 64 (BitVec.ofNat 16 v)).toNat = v := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have e16 : (2:Nat) ^ 16 = 65536 := by decide
    rw [e16, Nat.mod_eq_of_lt hv]
    exact Nat.mod_eq_of_lt (by omega)
  have hm : (18446744073709486080#64).toNat = 18446744073709486080 := rfl
  rw [BitVec.toNat_or, BitVec.toNat_and, h1, hm]
  have e := @Nat.or_mod_two_pow (x.toNat &&& 18446744073709486080) v 16
  simp only [Nat.reducePow] at e
  rw [e, @Nat.and_mod_two_pow x.toNat 18446744073709486080 16]
  simp only [Nat.reducePow]
  have : 18446744073709486080 % 65536 = 0 := by decide
  rw [this, Nat.and_zero, Nat.zero_or, Nat.mod_eq_of_lt hv]

open Janus.Arm64 in
theorem one_copy (M : Janus.Arm64.Memory) (d s n : Nat) :
    ∀ i, i < n → (M.writeLE d n (M.readLE s n)).readLE (d + i) 1 = M.readLE (s + i) 1 := by
  intro i hi
  rw [Memory.readLE_writeLE_inside _ _ (by omega) (by omega), show d + i - d = i by omega,
    readLE_byte_of_window M s n i hi]

theorem mod32_read (M : Janus.Arm64.Memory) (a : Nat) : M.readLE a 4 % 4294967296 = M.readLE a 4 :=
  Nat.mod_eq_of_lt (by simpa using Janus.Arm64.Memory.readLE_lt M a 4)

theorem mod64_read (M : Janus.Arm64.Memory) (a : Nat) : M.readLE a 8 % 18446744073709551616 = M.readLE a 8 :=
  Nat.mod_eq_of_lt (by simpa using Janus.Arm64.Memory.readLE_lt M a 8)

end Fv256.E
