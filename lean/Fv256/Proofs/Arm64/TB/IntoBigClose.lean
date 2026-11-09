import Fv256.Proofs.Arm64.TB.IntoBigDefs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.IntoBig

/-- The memory after the copy of the four words into the fresh array and the `len`/`cap` stores. -/
def M0 (W : Memory) (A' P len v0 v1 v2 v3 : Nat) : Memory :=
  (((((W.writeLE A' 8 v0).writeLE (A' + 8) 8 v1).writeLE (A' + 16) 8 v2).writeLE (A' + 24) 8 v3).writeLE
    (P + 16) 8 len).writeLE (P + 24) 8 4

theorem m0_bp (W : Memory) (A' P bp len v0 v1 v2 v3 : Nat) (hbA : Apart bp 8 A' 32) (hbP : Apart bp 8 P 32) :
    (M0 W A' P len v0 v1 v2 v3).readLE bp 8 = W.readLE bp 8 := by
  unfold M0 Apart at *
  rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
    read_words4 _ _ _ _ _ _ _ _ (by omega)]

theorem m0_len (W : Memory) (A' P len v0 v1 v2 v3 : Nat) (hlen : len < 2 ^ 64) :
    (M0 W A' P len v0 v1 v2 v3).readLE (P + 16) 8 = len := by
  unfold M0
  rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
    show (256 : Nat) ^ 8 = 2 ^ 64 by decide, Nat.mod_eq_of_lt hlen]

theorem m0_cap (W : Memory) (A' P len v0 v1 v2 v3 : Nat) :
    (M0 W A' P len v0 v1 v2 v3).readLE (P + 24) 8 = 4 := by
  unfold M0
  rw [Janus.Arm64.Memory.readLE_writeLE_self, show (256 : Nat) ^ 8 = 2 ^ 64 by decide]

theorem m0_words (W : Memory) (A' P len v0 v1 v2 v3 : Nat) (h0 : v0 < 2 ^ 64) (h1 : v1 < 2 ^ 64) (h2 : v2 < 2 ^ 64)
    (h3 : v3 < 2 ^ 64) (hAP : Apart A' 32 P 32) (i : Nat) (hi : i < 4) :
    (M0 W A' P len v0 v1 v2 v3).readLE (A' + 8 * i) 8
      = (if i = 0 then v0 else if i = 1 then v1 else if i = 2 then v2 else v3) := by
  unfold M0 Apart at *
  rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  exact words4 W A' v0 v1 v2 v3 h0 h1 h2 h3 i hi

theorem m0_acc (W : Memory) (A' P len v0 v1 v2 v3 a n : Nat) (w : Bool) :
    (M0 W A' P len v0 v1 v2 v3).accessible a n w = W.accessible a n w := by
  unfold M0
  simp only [Janus.Arm64.Memory.accessible_writeLE]

/-- The closing step of the allocating path: `X` is the memory just before the stores `abs.ptr = A'`, `neg = false`. -/
theorem bigout_slow (X : Memory) (bp P A' len v : Nat) (limb : Nat → Nat)
    (hbp : X.readLE bp 8 = P) (haccP : X.accessible P 32 true = true) (hP48 : P + 32 ≤ 2 ^ 48)
    (haccA : X.accessible A' 32 true = true) (hA48 : A' + 32 ≤ 2 ^ 48)
    (h16 : X.readLE (P + 16) 8 = len) (h24 : X.readLE (P + 24) 8 = 4)
    (hw : ∀ i, i < 4 → X.readLE (A' + 8 * i) 8 = limb i) (hlen : len ≤ 4)
    (hnorm : len = 0 ∨ limb (len - 1) ≠ 0) (hz : ∀ i, len ≤ i → i < 4 → limb i = 0)
    (hv : v = Fv256.C.bigAbs limb 4) (hbP : Apart bp 8 P 32) (hAP : Apart A' 32 P 32) :
    BigOut ((X.writeLE (P + 8) 8 A').writeLE P 1 0) bp P v := by
  unfold Apart at hbP hAP
  have hA : A' < 2 ^ 64 := by omega
  refine bigout_of _ bp P A' len 4 v limb ?_ ?_ hP48 ?_ ?_ ?_ ?_ (by omega) ?_ hA48 hlen ?_ hnorm hz hv
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact hbp
  · simp only [Janus.Arm64.Memory.accessible_writeLE]; exact haccP
  · rw [Janus.Arm64.Memory.readLE_writeLE_self]
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 by decide, Nat.mod_eq_of_lt hA]
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact h16
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact h24
  · simp only [Janus.Arm64.Memory.accessible_writeLE]; exact haccA
  · intro i hi
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact hw i hi

/-- Reading a block that the first runtime call (`newobject`) cannot touch: outside the runtime ranges, the stack
window and the two argument spill slots, the memory after the call reads as before it. -/
theorem read_call {M w2 : Memory} {rt : List (Nat × Nat)} {l1 h1 l2 h2 x n : Nat}
    (hf : MemFrame M w2 (rt ++ [(l1, h1), (l2, h2)])) (hx : Outside x n rt)
    (hw1 : x + n ≤ l1 ∨ h1 ≤ x) (hw2 : x + n ≤ l2 ∨ h2 ≤ x) : w2.readLE x n = M.readLE x n := by
  refine hf.readLE x n ?_
  simp only [outside_append, outside_cons, outside_nil, and_true]
  exact ⟨hx, hw1, hw2⟩

/-- Reading a block outside the runtime ranges and the stack window across a barrier call. -/
theorem read_wb' {M w3 : Memory} {rt : List (Nat × Nat)} {l h x n : Nat}
    (hf : MemFrame M w3 (rt ++ [(l, h)])) (hx : Outside x n rt) (hw : x + n ≤ l ∨ h ≤ x) :
    w3.readLE x n = M.readLE x n := by
  refine hf.readLE x n ?_
  simp only [outside_append, outside_cons, outside_nil, and_true]
  exact ⟨hx, hw⟩

set_option maxRecDepth 100000 in
/-- The in-memory result of the allocating path, when no barrier call is needed (flag clear). -/
theorem slow0_bigout {s S w2 : Memory} {rt : List (Nat × Nat)} {sp bp z P A' len v0 v1 v2 v3 : Nat}
    (hsp : 4144 ≤ sp)
    (hF : MemFrame S w2 (rt ++ [(sp - 48 - 4096, sp - 48 - 8), (sp - 48 + 8, sp - 48 + 8 + 8)]))
    (hfr : MemFrame s S (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8)]))
    (h_rdP : S.readLE bp 8 = P)
    (hbpo : Outside bp 8 rt) (hbpd : bp + 8 ≤ sp - 4144 ∨ sp - 4144 + 4168 ≤ bp)
    (hzo : Outside z 32 rt) (hzd : z + 32 ≤ sp - 4144 ∨ sp - 4144 + 4168 ≤ z) (hzb : z + 32 ≤ bp ∨ bp + 8 ≤ z)
    (hPa : s.accessible P 32 true = true) (hP48 : P + 32 ≤ 2 ^ 48)
    (hAacc : s.accessible A' 32 true = true) (hA48 : A' + 32 ≤ 2 ^ 48)
    (hbA : Apart bp 8 A' 32) (hbP : Apart bp 8 P 32) (hAP : Apart A' 32 P 32)
    (hlen : len ≤ 4)
    (hv : ∀ k, k < 4 → (if k = 0 then v0 else if k = 1 then v1 else if k = 2 then v2 else v3)
        = w2.readLE (z + 8 * k) 8)
    (hnorm : len = 0 ∨ w2.readLE (z + 8 * (len - 1)) 8 ≠ 0)
    (hzero : ∀ i, len ≤ i → i < 4 → w2.readLE (z + 8 * i) 8 = 0)
    (hv0 : v0 < 2 ^ 64) (hv1 : v1 < 2 ^ 64) (hv2 : v2 < 2 ^ 64) (hv3 : v3 < 2 ^ 64) :
    BigOut (((M0 w2 A' P len v0 v1 v2 v3).writeLE (P + 8) 8 A').writeLE P 1 0) bp P (val256 s z) := by
  -- reads of z and of the bp slot in `w2` are those of `s`
  have hzr : ∀ i, i < 4 → w2.readLE (z + 8 * i) 8 = s.readLE (z + 8 * i) 8 := by
    intro i hi
    rw [read_call hF (Outside.of_sub hzo (by omega) (by omega)) (by omega) (by omega)]
    have hz1 : Outside (z + 8 * i) 8 (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8)]) := by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hzo (by omega) (by omega), by omega, by omega⟩
    exact hfr.readLE (z + 8 * i) 8 hz1
  have hbpw : w2.readLE bp 8 = P := by
    rw [read_call hF hbpo (by omega) (by omega)]; exact h_rdP
  refine bigout_slow _ bp P A' len (val256 s z) (fun i => s.readLE (z + 8 * i) 8) ?_ ?_ hP48 ?_ hA48
    (m0_len _ _ _ _ _ _ _ _ (by omega)) (m0_cap _ _ _ _ _ _ _ _) ?_ hlen ?_ ?_ (val256_bigAbs s z) hbP hAP
  · rw [m0_bp _ _ _ _ _ _ _ _ _ hbA hbP]; exact hbpw
  · rw [m0_acc, hF.accessible, hfr.accessible]; exact hPa
  · rw [m0_acc, hF.accessible, hfr.accessible]; exact hAacc
  · intro i hi
    rw [m0_words _ _ _ _ _ _ _ _ hv0 hv1 hv2 hv3 hAP i hi, hv i hi, hzr i hi]
  · rcases hnorm with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [← hzr _ (by omega)]; exact h
  · intro i h1 h2
    rw [← hzr i h2]; exact hzero i h1 h2

set_option maxRecDepth 100000 in
/-- The frame up to the `len`/`cap` stores. -/
theorem m0_frame {s S w2 : Memory} {rt : List (Nat × Nat)} {sp bp P0 A0 P A' len v0 v1 v2 v3 : Nat}
    (hsp : 4144 ≤ sp)
    (hF : MemFrame S w2 (rt ++ [(sp - 48 - 4096, sp - 48 - 8), (sp - 48 + 8, sp - 48 + 8 + 8)]))
    (hfr : MemFrame s S (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8)]))
    (hAin : InRanges A' 32 rt)
    (hPin : InRanges P 32 (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8), (P0, P0 + 32), (A0, A0 + 32)])) :
    MemFrame s (M0 w2 A' P len v0 v1 v2 v3)
      (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8), (P0, P0 + 32), (A0, A0 + 32)]) := by
  have hL : ∀ a n, Outside a n (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8), (P0, P0 + 32), (A0, A0 + 32)]) →
      Outside a n (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8)]) := by
    intro a n hh
    simp only [outside_append, outside_cons, outside_nil, and_true] at hh ⊢
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
  have h1 : MemFrame s S (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8), (P0, P0 + 32), (A0, A0 + 32)]) := hfr.mono hL
  have h2 : MemFrame s w2 (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8), (P0, P0 + 32), (A0, A0 + 32)]) := by
    refine h1.trans hF ?_
    intro a n hh
    refine ⟨hh, ?_⟩
    simp only [outside_append, outside_cons, outside_nil, and_true] at hh ⊢
    refine ⟨hh.1, ?_, ?_⟩
    · rcases hh.2.1 with h | h
      · left; omega
      · right; omega
    · rcases hh.2.1 with h | h
      · left; omega
      · right; omega
  obtain ⟨rA, hrA, hrA1, hrA2⟩ := hAin
  have hrA' : rA ∈ rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8), (P0, P0 + 32), (A0, A0 + 32)] := by simp [hrA]
  obtain ⟨rP, hrP, hrP1, hrP2⟩ := hPin
  unfold M0
  exact (((((h2.writeLE_inRanges _ ⟨rA, hrA', by omega, by omega⟩).writeLE_inRanges _ ⟨rA, hrA', by omega, by omega⟩).writeLE_inRanges _
    ⟨rA, hrA', by omega, by omega⟩).writeLE_inRanges _ ⟨rA, hrA', by omega, by omega⟩).writeLE_inRanges _
    ⟨rP, hrP, by omega, by omega⟩).writeLE_inRanges _ ⟨rP, hrP, by omega, by omega⟩

set_option maxRecDepth 100000 in
/-- The frame of the allocating path with the flag clear. -/
theorem slow0_frame {s S w2 : Memory} {rt : List (Nat × Nat)} {sp bp P0 A0 P A' len v0 v1 v2 v3 : Nat}
    (hsp : 4144 ≤ sp)
    (hF : MemFrame S w2 (rt ++ [(sp - 48 - 4096, sp - 48 - 8), (sp - 48 + 8, sp - 48 + 8 + 8)]))
    (hfr : MemFrame s S (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8)]))
    (hAin : InRanges A' 32 rt)
    (hPin : InRanges P 32 (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8), (P0, P0 + 32), (A0, A0 + 32)])) :
    MemFrame s (((M0 w2 A' P len v0 v1 v2 v3).writeLE (P + 8) 8 A').writeLE P 1 0)
      (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8), (P0, P0 + 32), (A0, A0 + 32)]) := by
  have h3 := m0_frame (len := len) (v0 := v0) (v1 := v1) (v2 := v2) (v3 := v3) hsp hF hfr hAin hPin
  obtain ⟨rP, hrP, hrP1, hrP2⟩ := hPin
  exact (h3.writeLE_inRanges _ ⟨rP, hrP, by omega, by omega⟩).writeLE_inRanges _ ⟨rP, hrP, by omega, by omega⟩

set_option maxRecDepth 100000 in
/-- The frame of the allocating path with the barrier call. -/
theorem slow1_frame {s S w2 M w3 : Memory} {rt : List (Nat × Nat)}
    {sp bp P0 A0 P A' len v0 v1 v2 v3 w6 a b : Nat}
    (hsp : 4144 ≤ sp)
    (hF : MemFrame S w2 (rt ++ [(sp - 48 - 4096, sp - 48 - 8), (sp - 48 + 8, sp - 48 + 8 + 8)]))
    (hfr : MemFrame s S (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8)]))
    (hAin : InRanges A' 32 rt)
    (hPin : InRanges P 32 (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8), (P0, P0 + 32), (A0, A0 + 32)]))
    (hM : M = M0 w2 A' P len v0 v1 v2 v3)
    (hF3 : MemFrame M w3 (rt ++ [(sp - 48 - 4096, sp - 48 - 8)])) (hs : InRanges w6 16 rt) :
    MemFrame s ((((w3.writeLE w6 8 a).writeLE (w6 + 8) 8 b).writeLE (P + 8) 8 A').writeLE P 1 0)
      (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8), (P0, P0 + 32), (A0, A0 + 32)]) := by
  have h3 := m0_frame (len := len) (v0 := v0) (v1 := v1) (v2 := v2) (v3 := v3) hsp hF hfr hAin hPin
  rw [← hM] at h3
  have h4 : MemFrame s w3 (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8), (P0, P0 + 32), (A0, A0 + 32)]) := by
    refine h3.trans hF3 ?_
    intro a' n hh
    refine ⟨hh, ?_⟩
    simp only [outside_append, outside_cons, outside_nil, and_true] at hh ⊢
    refine ⟨hh.1, ?_⟩
    rcases hh.2.1 with h | h
    · left; omega
    · right; omega
  obtain ⟨rP, hrP, hrP1, hrP2⟩ := hPin
  obtain ⟨rS, hrS, hrS1, hrS2⟩ := hs
  have hrS' : rS ∈ rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8), (P0, P0 + 32), (A0, A0 + 32)] := by simp [hrS]
  exact (((h4.writeLE_inRanges _ ⟨rS, hrS', by omega, by omega⟩).writeLE_inRanges _ ⟨rS, hrS', by omega, by omega⟩).writeLE_inRanges _
    ⟨rP, hrP, by omega, by omega⟩).writeLE_inRanges _ ⟨rP, hrP, by omega, by omega⟩

theorem slots2_read (w : Memory) (w6 a b x n : Nat) (h : x + n ≤ w6 ∨ w6 + 16 ≤ x) :
    ((w.writeLE w6 8 a).writeLE (w6 + 8) 8 b).readLE x n = w.readLE x n := by
  rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]

set_option maxRecDepth 100000 in
/-- The in-memory result of the allocating path with the barrier call. -/
theorem slow1_bigout {s S w2 M w3 : Memory} {rt L1 : List (Nat × Nat)} {sp bp z P A' len v0 v1 v2 v3 w6 a b : Nat}
    (hsp : 4144 ≤ sp)
    (hF : MemFrame S w2 (rt ++ [(sp - 48 - 4096, sp - 48 - 8), (sp - 48 + 8, sp - 48 + 8 + 8)]))
    (hfr : MemFrame s S (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8)]))
    (h_rdP : S.readLE bp 8 = P)
    (hbpo : Outside bp 8 rt) (hbpd : bp + 8 ≤ sp - 4144 ∨ sp - 4144 + 4168 ≤ bp)
    (hzo : Outside z 32 rt) (hzd : z + 32 ≤ sp - 4144 ∨ sp - 4144 + 4168 ≤ z) (hzb : z + 32 ≤ bp ∨ bp + 8 ≤ z)
    (hPa : s.accessible P 32 true = true) (hP48 : P + 32 ≤ 2 ^ 48)
    (hAacc : s.accessible A' 32 true = true) (hA48 : A' + 32 ≤ 2 ^ 48)
    (hbA : Apart bp 8 A' 32) (hbP : Apart bp 8 P 32) (hAP : Apart A' 32 P 32)
    (hlen : len ≤ 4)
    (hv : ∀ k, k < 4 → (if k = 0 then v0 else if k = 1 then v1 else if k = 2 then v2 else v3)
        = w2.readLE (z + 8 * k) 8)
    (hnorm : len = 0 ∨ w2.readLE (z + 8 * (len - 1)) 8 ≠ 0)
    (hzero : ∀ i, len ≤ i → i < 4 → w2.readLE (z + 8 * i) 8 = 0)
    (hv0 : v0 < 2 ^ 64) (hv1 : v1 < 2 ^ 64) (hv2 : v2 < 2 ^ 64) (hv3 : v3 < 2 ^ 64)
    (hM : M = M0 w2 A' P len v0 v1 v2 v3)
    (hF3 : MemFrame M w3 (rt ++ [(sp - 48 - 4096, sp - 48 - 8)]))
    (hLive : LiveFrame M w3 L1 []) (hAL1 : InRanges A' 32 L1)
    (hs : InRanges w6 16 rt)
    (hPk16 : w3.readLE (P + 16) 8 = M.readLE (P + 16) 8) (hPk24 : w3.readLE (P + 24) 8 = M.readLE (P + 24) 8)
    (hAs : Apart A' 32 w6 16) (hPs : Apart P 32 w6 16) :
    BigOut ((((w3.writeLE w6 8 a).writeLE (w6 + 8) 8 b).writeLE (P + 8) 8 A').writeLE P 1 0) bp P (val256 s z) := by
  have hzr : ∀ i, i < 4 → w2.readLE (z + 8 * i) 8 = s.readLE (z + 8 * i) 8 := by
    intro i hi
    rw [read_call hF (Outside.of_sub hzo (by omega) (by omega)) (by omega) (by omega)]
    have hz1 : Outside (z + 8 * i) 8 (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8)]) := by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hzo (by omega) (by omega), by omega, by omega⟩
    exact hfr.readLE (z + 8 * i) 8 hz1
  have hbpw : w2.readLE bp 8 = P := by
    rw [read_call hF hbpo (by omega) (by omega)]; exact h_rdP
  obtain ⟨rS, hrS, hrS1, hrS2⟩ := hs
  have hbS := MemFrame.outside_mem hbpo hrS
  refine bigout_slow _ bp P A' len (val256 s z) (fun i => s.readLE (z + 8 * i) 8) ?_ ?_ hP48 ?_ hA48 ?_ ?_ ?_ hlen ?_ ?_
    (val256_bigAbs s z) hbP hAP
  · rw [slots2_read _ _ _ _ _ _ (by omega)]
    rw [read_wb' hF3 hbpo (by omega), hM, m0_bp _ _ _ _ _ _ _ _ _ hbA hbP]; exact hbpw
  · simp only [Janus.Arm64.Memory.accessible_writeLE]
    rw [hF3.accessible, hM, m0_acc, hF.accessible, hfr.accessible]; exact hPa
  · simp only [Janus.Arm64.Memory.accessible_writeLE]
    rw [hF3.accessible, hM, m0_acc, hF.accessible, hfr.accessible]; exact hAacc
  · rw [slots2_read _ _ _ _ _ _ (by unfold Apart at hPs; omega), hPk16, hM, m0_len _ _ _ _ _ _ _ _ (by omega)]
  · rw [slots2_read _ _ _ _ _ _ (by unfold Apart at hPs; omega), hPk24, hM, m0_cap]
  · intro i hi
    rw [slots2_read _ _ _ _ _ _ (by unfold Apart at hAs; omega)]
    obtain ⟨rL, hrL, hrL1, hrL2⟩ := hAL1
    rw [hLive.readLE _ 8 ⟨rL, hrL, by omega, by omega⟩ trivial, hM,
      m0_words _ _ _ _ _ _ _ _ hv0 hv1 hv2 hv3 hAP i hi, hv i hi, hzr i hi]
  · rcases hnorm with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [← hzr _ (by omega)]; exact h
  · intro i h1 h2
    rw [← hzr i h2]; exact hzero i h1 h2

/-- The memory after the `len`/`cap` stores of the tail. -/
def M1 (W : Memory) (P len : Nat) : Memory := (W.writeLE (P + 16) 8 len).writeLE (P + 24) 8 4

set_option maxRecDepth 100000 in
/-- The tail's result, no barrier call. -/
theorem tail0_bigout {s W : Memory} {sp bp z P A' len : Nat} {rt : List (Nat × Nat)}
    (hfr2 : MemFrame s W (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8)]))
    (h_rdP : W.readLE bp 8 = P)
    (hPa : s.accessible P 32 true = true) (hP48 : P + 32 ≤ 2 ^ 48)
    (hAacc : s.accessible A' 32 true = true) (hA48 : A' + 32 ≤ 2 ^ 48)
    (hbP : Apart bp 8 P 32) (hAP : Apart A' 32 P 32) (hlen : len ≤ 4)
    (hword : ∀ i, i < 4 → W.readLE (A' + 8 * i) 8 = s.readLE (z + 8 * i) 8)
    (hnorm : len = 0 ∨ s.readLE (z + 8 * (len - 1)) 8 ≠ 0)
    (hzero : ∀ i, len ≤ i → i < 4 → s.readLE (z + 8 * i) 8 = 0) :
    BigOut (((M1 W P len).writeLE (P + 8) 8 A').writeLE P 1 0) bp P (val256 s z) := by
  unfold Apart at hbP hAP
  have hlen' : len < 2 ^ 64 := by omega
  refine bigout_slow (M1 W P len) bp P A' len (val256 s z) (fun i => s.readLE (z + 8 * i) 8) ?_ ?_ hP48 ?_ hA48 ?_ ?_ ?_ hlen hnorm hzero (val256_bigAbs s z) (by unfold Apart; omega) (by unfold Apart; omega)
  · unfold M1
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact h_rdP
  · unfold M1; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hfr2.accessible]; exact hPa
  · unfold M1; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hfr2.accessible]; exact hAacc
  · unfold M1
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 by decide, Nat.mod_eq_of_lt hlen']
  · unfold M1
    rw [Janus.Arm64.Memory.readLE_writeLE_self, show (256 : Nat) ^ 8 = 2 ^ 64 by decide]
  · intro i hi
    unfold M1
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact hword i hi

set_option maxRecDepth 100000 in
/-- The tail's result with the barrier call. -/
theorem tail1_bigout {s W w3 : Memory} {sp bp z P A' len w6 a b : Nat} {rt L1 : List (Nat × Nat)}
    (hfr2 : MemFrame s W (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8)]))
    (h_rdP : W.readLE bp 8 = P)
    (hPa : s.accessible P 32 true = true) (hP48 : P + 32 ≤ 2 ^ 48)
    (hAacc : s.accessible A' 32 true = true) (hA48 : A' + 32 ≤ 2 ^ 48)
    (hbP : Apart bp 8 P 32) (hAP : Apart A' 32 P 32) (hlen : len ≤ 4)
    (hword : ∀ i, i < 4 → W.readLE (A' + 8 * i) 8 = s.readLE (z + 8 * i) 8)
    (hnorm : len = 0 ∨ s.readLE (z + 8 * (len - 1)) 8 ≠ 0)
    (hzero : ∀ i, len ≤ i → i < 4 → s.readLE (z + 8 * i) 8 = 0)
    (hbpo : Outside bp 8 rt) (hbpd : bp + 8 ≤ sp - 4144 ∨ sp - 4144 + 4168 ≤ bp) (hsp : 4144 ≤ sp)
    (hF3 : MemFrame (M1 W P len) w3 (rt ++ [(sp - 48 - 4096, sp - 48 - 8)]))
    (hLive : LiveFrame (M1 W P len) w3 L1 []) (hAL1 : InRanges A' 32 L1)
    (hs : InRanges w6 16 rt)
    (hPk16 : w3.readLE (P + 16) 8 = (M1 W P len).readLE (P + 16) 8)
    (hPk24 : w3.readLE (P + 24) 8 = (M1 W P len).readLE (P + 24) 8)
    (hAs : Apart A' 32 w6 16) (hPs : Apart P 32 w6 16) :
    BigOut ((((w3.writeLE w6 8 a).writeLE (w6 + 8) 8 b).writeLE (P + 8) 8 A').writeLE P 1 0) bp P (val256 s z) := by
  unfold Apart at hbP hAP hAs hPs
  have hlen' : len < 2 ^ 64 := by omega
  obtain ⟨rS, hrS, hrS1, hrS2⟩ := hs
  have hbS := MemFrame.outside_mem hbpo hrS
  refine bigout_slow ((w3.writeLE w6 8 a).writeLE (w6 + 8) 8 b) bp P A' len (val256 s z) (fun i => s.readLE (z + 8 * i) 8)
    ?_ ?_ hP48 ?_ hA48 ?_ ?_ ?_ hlen hnorm hzero (val256_bigAbs s z) (by unfold Apart; omega) (by unfold Apart; omega)
  · rw [slots2_read _ _ _ _ _ _ (by omega), read_wb' hF3 hbpo (by omega)]
    unfold M1
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact h_rdP
  · simp only [Janus.Arm64.Memory.accessible_writeLE]
    rw [hF3.accessible]; unfold M1; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hfr2.accessible]; exact hPa
  · simp only [Janus.Arm64.Memory.accessible_writeLE]
    rw [hF3.accessible]; unfold M1; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hfr2.accessible]; exact hAacc
  · rw [slots2_read _ _ _ _ _ _ (by omega), hPk16]
    unfold M1
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 by decide, Nat.mod_eq_of_lt hlen']
  · rw [slots2_read _ _ _ _ _ _ (by omega), hPk24]
    unfold M1
    rw [Janus.Arm64.Memory.readLE_writeLE_self, show (256 : Nat) ^ 8 = 2 ^ 64 by decide]
  · intro i hi
    rw [slots2_read _ _ _ _ _ _ (by omega)]
    obtain ⟨rL, hrL, hrL1, hrL2⟩ := hAL1
    rw [hLive.readLE _ 8 ⟨rL, hrL, by omega, by omega⟩ trivial]
    unfold M1
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact hword i hi

set_option maxRecDepth 100000 in
/-- The frame of the tail, no barrier call. -/
theorem tail0_frame {s W : Memory} {sp bp P A' len : Nat} {rt : List (Nat × Nat)}
    (hfr2 : MemFrame s W (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8)])) :
    MemFrame s (((M1 W P len).writeLE (P + 8) 8 A').writeLE P 1 0)
      (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8), (P, P + 32)]) := by
  have h1 := frame_add (al := P) (ah := P + 32) hfr2
  unfold M1
  exact (((h1.writeLE_inRanges _ ⟨(P, P + 32), by simp, by omega, by omega⟩).writeLE_inRanges _
    ⟨(P, P + 32), by simp, by omega, by omega⟩).writeLE_inRanges _ ⟨(P, P + 32), by simp, by omega, by omega⟩).writeLE_inRanges _
    ⟨(P, P + 32), by simp, by omega, by omega⟩

set_option maxRecDepth 100000 in
/-- The frame of the tail with the barrier call. -/
theorem tail1_frame {s W w3 : Memory} {sp bp P A' len w6 a b : Nat} {rt : List (Nat × Nat)}
    (hfr2 : MemFrame s W (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8)])) (hsp : 4144 ≤ sp)
    (hF3 : MemFrame (M1 W P len) w3 (rt ++ [(sp - 48 - 4096, sp - 48 - 8)])) (hs : InRanges w6 16 rt) :
    MemFrame s ((((w3.writeLE w6 8 a).writeLE (w6 + 8) 8 b).writeLE (P + 8) 8 A').writeLE P 1 0)
      (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8), (P, P + 32)]) := by
  have h1 := frame_add (al := P) (ah := P + 32) hfr2
  have h2 : MemFrame s (M1 W P len) (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8), (P, P + 32)]) := by
    unfold M1
    exact (h1.writeLE_inRanges _ ⟨(P, P + 32), by simp, by omega, by omega⟩).writeLE_inRanges _
      ⟨(P, P + 32), by simp, by omega, by omega⟩
  have h4 : MemFrame s w3 (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8), (P, P + 32)]) := by
    refine h2.trans hF3 ?_
    intro a' n hh
    refine ⟨hh, ?_⟩
    simp only [outside_append, outside_cons, outside_nil, and_true] at hh ⊢
    refine ⟨hh.1, ?_⟩
    rcases hh.2.1 with h | h
    · left; omega
    · right; omega
  obtain ⟨rS, hrS, hrS1, hrS2⟩ := hs
  have hrS' : rS ∈ rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8), (P, P + 32)] := by simp [hrS]
  exact (((h4.writeLE_inRanges _ ⟨rS, hrS', by omega, by omega⟩).writeLE_inRanges _ ⟨rS, hrS', by omega, by omega⟩).writeLE_inRanges _
    ⟨(P, P + 32), by simp, by omega, by omega⟩).writeLE_inRanges _ ⟨(P, P + 32), by simp, by omega, by omega⟩

set_option maxRecDepth 100000 in
/-- The frame after the first runtime call and the four-word copy (allocating path, state at the tail). -/
theorem frame_s2 {s S w2 : Memory} {rt : List (Nat × Nat)} {sp bp A v0 v1 v2 v3 : Nat}
    (hsp : 4144 ≤ sp)
    (hF : MemFrame S w2 (rt ++ [(sp - 48 - 4096, sp - 48 - 8), (sp - 48 + 8, sp - 48 + 8 + 8)]))
    (hfr : MemFrame s S (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8)]))
    (hA : InRanges A 32 rt) :
    MemFrame s ((((w2.writeLE A 8 v0).writeLE (A + 8) 8 v1).writeLE (A + 16) 8 v2).writeLE (A + 24) 8 v3)
      (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8)]) := by
  have h2 : MemFrame s w2 (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8)]) := by
    refine hfr.trans hF ?_
    intro a n hh
    refine ⟨hh, ?_⟩
    simp only [outside_append, outside_cons, outside_nil, and_true] at hh ⊢
    refine ⟨hh.1, ?_, ?_⟩
    · rcases hh.2.1 with h | h
      · left; omega
      · right; omega
    · rcases hh.2.1 with h | h
      · left; omega
      · right; omega
  obtain ⟨rA, hrA, hrA1, hrA2⟩ := hA
  have hrA' : rA ∈ rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8)] := by simp [hrA]
  exact (((h2.writeLE_inRanges _ ⟨rA, hrA', by omega, by omega⟩).writeLE_inRanges _ ⟨rA, hrA', by omega, by omega⟩).writeLE_inRanges _
    ⟨rA, hrA', by omega, by omega⟩).writeLE_inRanges _ ⟨rA, hrA', by omega, by omega⟩

theorem view_words4_live (rt L : List (Nat × Nat)) (M : Memory) (A v0 v1 v2 v3 : Nat) (hA : InRanges A 32 L) :
    view rt L ((((M.writeLE A 8 v0).writeLE (A + 8) 8 v1).writeLE (A + 16) 8 v2).writeLE (A + 24) 8 v3) = view rt L M := by
  obtain ⟨r, hr, h1, h2⟩ := hA
  rw [view_writeLE_live ⟨r, hr, by omega, by omega⟩, view_writeLE_live ⟨r, hr, by omega, by omega⟩,
    view_writeLE_live ⟨r, hr, by omega, by omega⟩, view_writeLE_live ⟨r, hr, by omega, by omega⟩]

set_option maxRecDepth 100000 in
/-- The limbs of `z` are the same in `s`, `S` and `w2` (across the first runtime call). -/
theorem s2_zr {s S w2 : Memory} {rt : List (Nat × Nat)} {sp bp z : Nat}
    (hF : MemFrame S w2 (rt ++ [(sp - 48 - 4096, sp - 48 - 8), (sp - 48 + 8, sp - 48 + 8 + 8)]))
    (hfr : MemFrame s S (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8)]))
    (hsp : 4144 ≤ sp) (hzo : Outside z 32 rt) (hzd : z + 32 ≤ sp - 4144 ∨ sp - 4144 + 4168 ≤ z)
    (hzb : z + 32 ≤ bp ∨ bp + 8 ≤ z) :
    ∀ i, i < 4 → w2.readLE (z + 8 * i) 8 = s.readLE (z + 8 * i) 8 := by
  intro i hi
  rw [read_call hF (Outside.of_sub hzo (by omega) (by omega)) (by omega) (by omega)]
  have hz1 : Outside (z + 8 * i) 8 (rt ++ [(sp - 4144, sp - 8), (sp + 8, sp + 24), (bp, bp + 8)]) := by
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨Outside.of_sub hzo (by omega) (by omega), by omega, by omega⟩
  exact hfr.readLE (z + 8 * i) 8 hz1

set_option maxRecDepth 100000 in
/-- The copied words read back as the limbs of `z`. -/
theorem s2_word {s M : Memory} {z A v0 v1 v2 v3 : Nat}
    (hzr : ∀ i, i < 4 → M.readLE (z + 8 * i) 8 = s.readLE (z + 8 * i) 8)
    (hv0 : v0 < 2 ^ 64) (hv1 : v1 < 2 ^ 64) (hv2 : v2 < 2 ^ 64) (hv3 : v3 < 2 ^ 64)
    (hv : ∀ k, k < 4 → (if k = 0 then v0 else if k = 1 then v1 else if k = 2 then v2 else v3) = M.readLE (z + 8 * k) 8) :
    ∀ i, i < 4 → ((((M.writeLE A 8 v0).writeLE (A + 8) 8 v1).writeLE (A + 16) 8 v2).writeLE (A + 24) 8 v3).readLE (A + 8 * i) 8
      = s.readLE (z + 8 * i) 8 := by
  intro i hi
  rw [words4 _ _ _ _ _ _ hv0 hv1 hv2 hv3 i hi, hv i hi, hzr i hi]

theorem lt4_cases (k : Nat) (hk : k < 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega

theorem le48 (a : Nat) (h : a ≤ 281474976710624) : a + 32 ≤ 2 ^ 48 := by omega

theorem tn (len : Nat) (h : len ≤ 4) : (BitVec.ofNat 64 len).toNat = len := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

/-- A stack slot is the same before the first runtime call and after the call and the four-word copy. -/
theorem s2_slot {S w2 : Memory} {rt : List (Nat × Nat)} {sp A x v0 v1 v2 v3 : Nat}
    (hF : MemFrame S w2 (rt ++ [(sp - 48 - 4096, sp - 48 - 8), (sp - 48 + 8, sp - 48 + 8 + 8)]))
    (hout : Outside (sp - 4144) 4168 rt) (hA : Apart (sp - 4144) 4168 A 32) (hsp : 4144 ≤ sp)
    (hx1 : sp - 56 ≤ x) (hx2 : x + 8 ≤ sp + 24) (hx3 : x + 8 ≤ sp - 40 ∨ sp - 32 ≤ x) :
    ((((w2.writeLE A 8 v0).writeLE (A + 8) 8 v1).writeLE (A + 16) 8 v2).writeLE (A + 24) 8 v3).readLE x 8
      = S.readLE x 8 := by
  unfold Apart at hA
  rw [read_words4 _ _ _ _ _ _ _ _ (by omega),
    read_call hF (Outside.of_sub hout (by omega) (by omega)) (by omega) (by omega)]

theorem bp_arith {sp bp : Nat} (h : bp + 8 ≤ sp - 4144 ∨ sp - 4144 + 4168 ≤ bp) :
    (bp + 8 ≤ sp - 48 - 4096 ∨ sp - 48 - 8 ≤ bp) ∧ (bp + 8 ≤ sp - 48 + 8 ∨ sp - 48 + 8 + 8 ≤ bp) := by
  omega

/-- The slot `bp` is the same before and after the first runtime call and the copy. -/
theorem s2_bp {S w2 : Memory} {rt : List (Nat × Nat)} {sp A bp v0 v1 v2 v3 : Nat}
    (hF : MemFrame S w2 (rt ++ [(sp - 48 - 4096, sp - 48 - 8), (sp - 48 + 8, sp - 48 + 8 + 8)]))
    (hbpo : Outside bp 8 rt) (hbpd : bp + 8 ≤ sp - 4144 ∨ sp - 4144 + 4168 ≤ bp)
    (hbA : Apart bp 8 A 32) (hsp : 4144 ≤ sp) :
    ((((w2.writeLE A 8 v0).writeLE (A + 8) 8 v1).writeLE (A + 16) 8 v2).writeLE (A + 24) 8 v3).readLE bp 8
      = S.readLE bp 8 := by
  unfold Apart at hbA
  have h1 : bp + 8 ≤ A ∨ A + 32 ≤ bp := hbA
  obtain ⟨h2, h3⟩ := bp_arith hbpd
  rw [read_words4 _ _ _ _ _ _ _ _ h1, read_call hF hbpo h2 h3]

end Fv256.Arm64.IntoBig
