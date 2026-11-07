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

end Fv256.FormatFastA64
