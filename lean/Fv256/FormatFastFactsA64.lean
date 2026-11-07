import Fv256.FormatFastDefsA64

open Janus Janus.Arm64 Janus.Contracts Janus.Contracts.ICall Janus.Spec

namespace Fv256.FormatFastA64

theorem out_fl {rt : List (Nat × Nat)} {r stack a n : Nat} (ho : Outside a n rt)
    (hd : a + n ≤ r - stack ∨ r + 0x78 ≤ a) (h8 : 8 + stack ≤ r) : Outside a n (FL rt r stack) := by
  simp only [FL, outside_append, outside_cons, outside_nil]
  refine ⟨ho, ?_, ?_, ?_, trivial⟩ <;> omega

/-- the itab words and `*z` as seen at any later state of the fast path -/
theorem finv_tab {rt : List (Nat × Nat)} {stack : Nat} {z tab data : BitVec 64} {fW fP fF fWr ch : Nat} {S0 S : State}
    (hp : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch S0 S) :
    S.mem.readLE (tab.toNat + 0x18) 8 = fF ∧ S.mem.readLE (tab.toNat + 0x20) 8 = fP ∧
    S.mem.readLE (tab.toNat + 0x28) 8 = fW ∧ S.mem.readLE (tab.toNat + 0x30) 8 = fWr ∧
    S.mem.accessible (tab.toNat + 0x18) 32 false = true ∧
    S.mem.readLE z.toNat 32 = S0.mem.readLE z.toNat 32 ∧ S.mem.accessible z.toNat 32 false = true ∧
    S.mem.accessible (S0.sp.toNat - stack) (stack + 0x78) true = true := by
  obtain ⟨-, -, -, -, hal, -, hwb, hwn, hwa, hout, -, -, -, -, -, -, htb, hta, hF, hP, hW, hWr, hto, htd, hzp, hzo, hzd⟩ := hp
  obtain ⟨-, -, -, -, hfr, -⟩ := hi
  have ot : ∀ a n, tab.toNat + 0x18 ≤ a → a + n ≤ tab.toNat + 0x38 → Outside a n (FL rt S0.sp.toNat stack) :=
    fun a n h1 h2 => out_fl (hto.of_sub h1 h2) (by omega) hwb
  have oz : Outside z.toNat 32 (FL rt S0.sp.toNat stack) := out_fl hzo (by omega) hwb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr.readLE _ _ (ot _ _ (by omega) (by omega))]; exact hF
  · rw [hfr.readLE _ _ (ot _ _ (by omega) (by omega))]; exact hP
  · rw [hfr.readLE _ _ (ot _ _ (by omega) (by omega))]; exact hW
  · rw [hfr.readLE _ _ (ot _ _ (by omega) (by omega))]; exact hWr
  · rw [hfr.accessible]; exact hta
  · exact hfr.readLE _ _ oz
  · rw [hfr.accessible]; exact hzp.1
  · rw [hfr.accessible]; exact hwa


/-- a range inside the spill area `[r+88, r+116)` is outside the ranges a callee with the argument window `[r+8, e)` may write -/
theorem out_cs {rt : List (Nat × Nat)} {r stack a n e : Nat} (hout : Outside (r - stack) (stack + 0x78) rt)
    (h8 : 8 ≤ stack) (he : e ≤ r + 88) (h1 : r + 88 ≤ a) (h2 : a + n ≤ r + 116) :
    Outside a n (rt ++ [(r - stack, r - 8), (r + 8, e)]) := by
  simp only [outside_append, outside_cons, outside_nil]
  refine ⟨hout.of_sub (by omega) (by omega), ?_, ?_, trivial⟩ <;> omega

/-- the invariant survives a call whose frame is `rt ++ [(S0.sp - stack, S0.sp - 8), (S0.sp + 8, e)]` (`e ≤ S0.sp + 40`) and which keeps `SP, x29, x28, x18` -/
theorem finv_call {rt : List (Nat × Nat)} {stack : Nat} {z tab data : BitVec 64} {ch : Nat} {S0 S S' : State} {m : Memory}
    {e : Nat} (hi : FInv rt stack z tab data ch S0 S) (hst : 8 ≤ stack)
    (hout : Outside (S0.sp.toNat - stack) (stack + 0x78) rt) (he : e ≤ S0.sp.toNat + 40)
    (hfr : MemFrame S.mem m (rt ++ [(S0.sp.toNat - stack, S0.sp.toNat - 8), (S0.sp.toNat + 8, e)]))
    (hsp : S'.sp = S.sp) (h29 : S'.regs 29 = S.regs 29) (h28 : S'.regs 28 = S.regs 28) (h18 : S'.regs 18 = S.regs 18)
    (hm : S'.mem = m) : FInv rt stack z tab data ch S0 S' := by
  obtain ⟨a4, a29, a28, a18, afr, r88, r96, r104, r112⟩ := hi
  have hs : S.sp.toNat = S0.sp.toNat := by rw [a4]
  have h2 : MemFrame S.mem m (FL rt S0.sp.toNat stack) :=
    MemFrame.mono hfr (fun a n' h => by
      simp only [FL, outside_append, outside_cons, outside_nil] at h ⊢
      obtain ⟨h1, h2, h3, h4, -⟩ := h
      refine ⟨h1, h2, ?_, trivial⟩ <;> omega)
  have hr : ∀ a k, S0.sp.toNat + 88 ≤ a → a + k ≤ S0.sp.toNat + 116 → m.readLE a k = S.mem.readLE a k := by
    intro a k h1 h2
    exact hfr.readLE a k (by
      simp only [outside_append, outside_cons, outside_nil]
      exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega, trivial⟩)
  refine ⟨hsp.trans a4, h29.trans a29, h28.trans a28, h18.trans a18, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm]; exact afr.trans h2 fun a n h => ⟨h, h⟩
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r88
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r96
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r104
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r112


theorem lsb0_iff (x : BitVec 64) : (BitVec.getLsbD x 0 == true) = true ↔ x.toNat % 2 = 1 := by
  simp [BitVec.getLsbD]

theorem lsb0_xor (x : BitVec 64) : (BitVec.getLsbD (x ^^^ 1#64) 0 == true) = true ↔ x.toNat % 2 = 0 := by
  have h := lsb0_iff x
  simp at h ⊢
  have := Nat.mod_two_eq_zero_or_one x.toNat
  cases hx : x[0] <;> simp_all <;> omega


theorem finv_of {rt : List (Nat × Nat)} {stack : Nat} {z tab data : BitVec 64} {ch : Nat} {S0 S S' : State}
    (hi : FInv rt stack z tab data ch S0 S) (h4 : S'.sp = S.sp) (h29 : S'.regs 29 = S.regs 29)
    (h28 : S'.regs 28 = S.regs 28) (h18 : S'.regs 18 = S.regs 18) (hm : S'.mem = S.mem) :
    FInv rt stack z tab data ch S0 S' := by
  obtain ⟨a4, a29, a28, a18, afr, r88, r96, r104, r112⟩ := hi
  exact ⟨h4.trans a4, h29.trans a29, h28.trans a28, h18.trans a18, hm ▸ afr, hm ▸ r88, hm ▸ r96, hm ▸ r104, hm ▸ r112⟩

theorem lsb0_false (x : BitVec 64) : (BitVec.getLsbD x 0 == false) = true ↔ x.toNat % 2 = 0 := by
  have h := lsb0_iff x
  simp at h ⊢
  have := Nat.mod_two_eq_zero_or_one x.toNat
  cases hx : x[0] <;> simp_all <;> omega

theorem lsb0_xor_false (x : BitVec 64) : (BitVec.getLsbD (x ^^^ 1#64) 0 == false) = true ↔ x.toNat % 2 = 1 := by
  have h := lsb0_xor x
  simp at h ⊢
  have := Nat.mod_two_eq_zero_or_one x.toNat
  cases hx : x[0] <;> simp_all <;> omega

/-- the read-only data stays loaded across a memory frame that leaves the data ranges alone and keeps the regions -/
theorem dataLoaded_frame {p : Janus.Program} {m m' : Memory} {rs : List (Nat × Nat)} (h : p.DataLoaded m)
    (hr : m'.regions = m.regions) (hfr : MemFrame m m' rs) (ho : ∀ d ∈ p.data, Outside d.base d.bytes.length rs) :
    p.DataLoaded m' := by
  intro d hd
  obtain ⟨h1, h2⟩ := h d hd
  refine ⟨by rw [hr]; exact h1, fun i hi => ?_⟩
  have e := hfr.readLE (d.base + i) 1 ((ho d hd).of_sub (by omega) (by omega))
  rw [Janus.Arm64.Memory.readLE_one, Janus.Arm64.Memory.readLE_one] at e
  rw [e]; exact h2 i hi

/-- A writable range is disjoint from every read-only data object (`Program.DataLoaded`, arm64). -/
theorem dataLoaded_disjoint {p : Janus.Program} {m : Memory} (h : p.DataLoaded m) {d : Janus.DataSegment}
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

/-- the invariant survives a summary call whose frame is the single window `[S0.sp - k, S0.sp - 8)` (`k ≤ stack`) -/
theorem finv_call1 {rt : List (Nat × Nat)} {stack : Nat} {z tab data : BitVec 64} {ch : Nat} {S0 S S' : State} {m : Memory}
    {k : Nat} (hi : FInv rt stack z tab data ch S0 S) (hst : 8 ≤ stack)
    (hout : Outside (S0.sp.toNat - stack) (stack + 0x78) rt) (hk : k ≤ stack)
    (hfr : MemFrame S.mem m (rt ++ [(S0.sp.toNat - k, S0.sp.toNat - 8)]))
    (hsp : S'.sp = S.sp) (h29 : S'.regs 29 = S.regs 29) (h28 : S'.regs 28 = S.regs 28) (h18 : S'.regs 18 = S.regs 18)
    (hm : S'.mem = m) : FInv rt stack z tab data ch S0 S' := by
  obtain ⟨a4, a29, a28, a18, afr, r88, r96, r104, r112⟩ := hi
  have h2 : MemFrame S.mem m (FL rt S0.sp.toNat stack) :=
    MemFrame.mono hfr (fun a n' h => by
      simp only [FL, outside_append, outside_cons, outside_nil] at h ⊢
      obtain ⟨h1, h2, h3, h4, -⟩ := h
      refine ⟨h1, ?_, trivial⟩ <;> omega)
  have hr : ∀ a k', S0.sp.toNat + 88 ≤ a → a + k' ≤ S0.sp.toNat + 116 → m.readLE a k' = S.mem.readLE a k' := by
    intro a k' h1 h2
    exact hfr.readLE a k' (by
      simp only [outside_append, outside_cons, outside_nil]
      exact ⟨hout.of_sub (by omega) (by omega), by omega, trivial⟩)
  refine ⟨hsp.trans a4, h29.trans a29, h28.trans a28, h18.trans a18, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm]; exact afr.trans h2 fun a n h => ⟨h, h⟩
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r88
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r96
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r104
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r112

/-- `finv_call` for a callee window `[S0.sp - k, S0.sp - 8)` with `k ≤ stack` -/
theorem finv_call_k {rt : List (Nat × Nat)} {stack : Nat} {z tab data : BitVec 64} {ch : Nat} {S0 S S' : State} {m : Memory}
    {e k : Nat} (hi : FInv rt stack z tab data ch S0 S) (hst : 8 ≤ stack)
    (hout : Outside (S0.sp.toNat - stack) (stack + 0x78) rt) (hk : k ≤ stack) (he : e ≤ S0.sp.toNat + 40)
    (hfr : MemFrame S.mem m (rt ++ [(S0.sp.toNat - k, S0.sp.toNat - 8), (S0.sp.toNat + 8, e)]))
    (hsp : S'.sp = S.sp) (h29 : S'.regs 29 = S.regs 29) (h28 : S'.regs 28 = S.regs 28) (h18 : S'.regs 18 = S.regs 18)
    (hm : S'.mem = m) : FInv rt stack z tab data ch S0 S' := by
  obtain ⟨a4, a29, a28, a18, afr, r88, r96, r104, r112⟩ := hi
  have h2 : MemFrame S.mem m (FL rt S0.sp.toNat stack) :=
    MemFrame.mono hfr (fun a n' h => by
      simp only [FL, outside_append, outside_cons, outside_nil] at h ⊢
      obtain ⟨h1, h2, h3, h4, -⟩ := h
      refine ⟨h1, ?_, ?_, trivial⟩ <;> omega)
  have hr : ∀ a k', S0.sp.toNat + 88 ≤ a → a + k' ≤ S0.sp.toNat + 116 → m.readLE a k' = S.mem.readLE a k' := by
    intro a k' h1 h2
    exact hfr.readLE a k' (by
      simp only [outside_append, outside_cons, outside_nil]
      exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega, trivial⟩)
  refine ⟨hsp.trans a4, h29.trans a29, h28.trans a28, h18.trans a18, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm]; exact afr.trans h2 fun a n h => ⟨h, h⟩
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r88
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r96
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r104
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r112

/-- the saved slots `[r - 8, r + 8)` (`x29` at `r - 8`, `x30` at `r`) are outside the frame list -/
theorem out_fl_save {rt : List (Nat × Nat)} {r stack a n : Nat} (ho : Outside a n rt)
    (h1 : r - 8 ≤ a) (h2 : a + n ≤ r + 8) (hst : 8 ≤ stack) : Outside a n (FL rt r stack) := by
  simp only [FL, outside_append, outside_cons, outside_nil]
  refine ⟨ho, ?_, ?_, ?_, trivial⟩ <;> omega

theorem frame_call {rt : List (Nat × Nat)} {stack : Nat} {S0 S : State} {m : Memory} {e : Nat}
    (afr : MemFrame S0.mem S.mem (FL rt S0.sp.toNat stack)) (he : e ≤ S0.sp.toNat + 40)
    (hfr : MemFrame S.mem m (rt ++ [(S0.sp.toNat - stack, S0.sp.toNat - 8), (S0.sp.toNat + 8, e)])) :
    MemFrame S0.mem m (FL rt S0.sp.toNat stack) := by
  have h2 : MemFrame S.mem m (FL rt S0.sp.toNat stack) :=
    MemFrame.mono hfr (fun a n' h => by
      simp only [FL, outside_append, outside_cons, outside_nil] at h ⊢
      obtain ⟨h1, h2, h3, h4, -⟩ := h
      refine ⟨h1, h2, ?_, trivial⟩ <;> omega)
  exact afr.trans h2 fun a n h => ⟨h, h⟩

section hexfacts
open Fv256.FormatSpec
theorem strBytes_drop2 (m : Janus.Arm64.Memory) (p n : Nat) :
    Janus.Spec.strBytes m (p + 2) n = (Janus.Spec.strBytes m p (n + 2)).drop 2 := by
  apply List.ext_getElem
  · simp [Janus.Spec.strBytes]
  · intro i h1 h2
    simp only [Janus.Spec.strBytes, List.getElem_drop, List.getElem_map, List.getElem_range]
    congr 2
    omega

theorem hexDigits_le64 (v n : Nat) (hv : v < 2 ^ 256) (h : Fv256.C.hexDigits v n) : n ≤ 64 := by
  obtain ⟨h1, h2, h3⟩ := h
  refine Decidable.byContradiction fun hn => ?_
  have : 16 ^ 64 ≤ 16 ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have e : (16 : Nat) ^ 64 = 2 ^ 256 := by decide
  rcases h3 with h3 | h3
  · omega
  · omega

theorem hexBytes_digits : ∀ (n z : Nat), Fv256.C.hexDigits z n →
    hexBytes z = (List.range n).map (fun k => Fv256.C.hexChar (z / 16 ^ (n - 1 - k) % 16)) := by
  intro n
  induction n with
  | zero => intro z h; exact absurd h.1 (by omega)
  | succ n ih =>
    intro z h
    obtain ⟨h1, h2, h3⟩ := h
    by_cases hn : n = 0
    · subst hn
      have hz : z < 16 := by simpa using h2
      rw [hexBytes]; simp [hz, Fv256.C.hexChar, Nat.mod_eq_of_lt hz]
    · have hpow : 16 ^ n = 16 * 16 ^ (n - 1) := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel, Nat.pow_succ]; omega
      have hp1 : 1 ≤ 16 ^ (n - 1) := Nat.one_le_pow _ _ (by omega)
      have h3' : 16 ^ n ≤ z := by
        rcases h3 with h3 | h3
        · omega
        · simpa using h3
      have hz : 16 ≤ z := by omega
      have hd : Fv256.C.hexDigits (z / 16) n := by
        refine ⟨by omega, ?_, Or.inr ?_⟩
        · rw [Nat.pow_succ] at h2; omega
        · omega
      rw [hexBytes, dif_neg (by omega), ih (z / 16) hd, List.range_succ, List.map_append]
      congr 1
      · apply List.map_congr_left
        intro k hk
        have hk' := List.mem_range.mp hk
        rw [Nat.div_div_eq_div_mul]
        have e : 16 * 16 ^ (n - 1 - k) = 16 ^ (n + 1 - 1 - k) := by
          obtain ⟨j, hj⟩ : ∃ j, n - k = j + 1 := ⟨n - k - 1, by omega⟩
          have e1 : n - 1 - k = j := by omega
          have e2 : n + 1 - 1 - k = j + 1 := by omega
          rw [e1, e2, Nat.pow_succ]; omega
        rw [e]
      · simp [Fv256.C.hexChar]


end hexfacts

end Fv256.FormatFastA64
