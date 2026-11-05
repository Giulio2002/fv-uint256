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

end Fv256.E
