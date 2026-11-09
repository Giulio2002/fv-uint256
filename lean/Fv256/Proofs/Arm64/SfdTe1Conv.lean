import Fv256.Proofs.Arm64.SfdTe1Mem
import Fv256.Proofs.Arm64.SfdTeObj0

/-!
# `strconv.toError`, write-barrier branch (arm64): the `TePost` of the finished object (extraction-free)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.Arm64.SfdEnv

namespace Fv256.Arm64.SfdToError

open Fv256.Amd64.SfdToError in
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem te1_conv {R : RtInv} {R2 : IfaceModel} {b : Nat} {L : List (Nat × Nat)} {fp fl sp sl : BitVec 64}
    {s S s' : State} {m' m2 m3 m4 m5 m6 : Janus.Arm64.Memory} {q t buf buf1 : BitVec 64}
    (F : Pre1 R R2 b L fp fl sp sl s S m' m2 m3 m4 q t)
    (hMF5 : MemFrame (m4.writeLE (t.toNat + 8) 8 fl.toNat) m5
      (R.rt ++ [(s.sp.toNat - 96 - 4096, s.sp.toNat - 96 - 8)]))
    (hLF5 : LiveFrame (m4.writeLE (t.toNat + 8) 8 fl.toNat) m5
      (L ++ [(q.toNat, q.toNat + blockSize sl.toNat true)] ++ [(t.toNat, t.toNat + 48)]) [])
    (hB5 : InRanges buf.toNat 16 R.rt) (hAt5 : Apart buf.toNat 16 t.toNat 48)
    (hAq5 : Apart buf.toNat 16 q.toNat (blockSize sl.toNat true))
    (hMF6 : MemFrame (CH m5 buf.toNat t.toNat fp.toNat q.toNat sl.toNat (s.mem.readLE strconvErrSyntax 8)) m6
      (R.rt ++ [(s.sp.toNat - 96 - 4096, s.sp.toNat - 96 - 8)]))
    (hLF6 : LiveFrame (CH m5 buf.toNat t.toNat fp.toNat q.toNat sl.toNat (s.mem.readLE strconvErrSyntax 8)) m6
      (L ++ [(q.toNat, q.toNat + blockSize sl.toNat true)] ++ [(t.toNat, t.toNat + 48)]) [])
    (hB6 : InRanges buf1.toNat 8 R.rt)
    (hAL6 : (ApartAll buf1.toNat 8 L ∧ Apart buf1.toNat 8 q.toNat (blockSize sl.toNat true)) ∧ Apart buf1.toNat 8 t.toNat 48)
    (hIS6 : InvSlots R (b - blockSize sl.toNat true - 48)
      (L ++ [(q.toNat, q.toNat + blockSize sl.toNat true)] ++ [(t.toNat, t.toNat + 48)]) (s.regs 28).toNat R.rt m6 buf1.toNat 1)
    (hsp' : s'.sp = s.sp) (hr29 : s'.regs 29 = s.regs 29) (hr28 : s'.regs 28 = s.regs 28) (hr18 : s'.regs 18 = s.regs 18)
    (hr0 : s'.regs 0 = BitVec.ofNat 64 numErrItab) (hr1 : s'.regs 1 = t)
    (hm : s'.mem = FM m6 buf1.toNat t.toNat (s.mem.readLE (strconvErrSyntax + 8) 8)) :
    TePost R R2 b L fp fl sp sl s s' := by
  obtain ⟨hdep, hlow, e9, e10, hSf, hfr, hMF1, hMF2, hMF3, hLF1, hLF3, hCop, hinvN, hInR, hInT, hApL, hApT, hQsl, hspR, hspP,
    hsdisj, hSm8, oE, pE, qE, hf4, hacc4, hacc4t, hacc4e, hacc4w, hlr4, hfp4, hts4, hte4, hwF, hL18, hrt0, hal, hsp72, e5, pW, qW, hSrec, oW⟩ := F
  have b48 : blockSize 48 false = 48 := by decide
  have qlt : q.toNat < 2 ^ 64 := q.isLt
  have hbase := te0_base hSf hfr hMF1 hMF2 hMF3 hdep hlow hInR hQsl
  rw [b48] at hInT
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ := inRanges_fields hInT (rs' := R.rt ++ R2.priv ++ [(s.sp.toNat - 4192, s.sp.toNat + 72)])
    (fun r hr => by simp [hr])
  have hB5' : InRanges buf.toNat 8 (R.rt ++ R2.priv ++ [(s.sp.toNat - 4192, s.sp.toNat + 72)]) :=
    InRanges.of_subset (Fv256.Amd64.SfdToError.inRanges16_lo hB5) (by intro r hr; simp [hr])
  have hB5'' : InRanges (buf.toNat + 8) 8 (R.rt ++ R2.priv ++ [(s.sp.toNat - 4192, s.sp.toNat + 72)]) :=
    InRanges.of_subset (Fv256.Amd64.SfdToError.inRanges16_hi hB5) (by intro r hr; simp [hr])
  have hB6' : InRanges buf1.toNat 8 (R.rt ++ R2.priv ++ [(s.sp.toNat - 4192, s.sp.toNat + 72)]) :=
    InRanges.of_subset hB6 (by intro r hr; simp [hr])
  have hW : (s.sp.toNat - 4192, s.sp.toNat + 72) ∈ R.rt ++ R2.priv ++ [(s.sp.toNat - 4192, s.sp.toNat + 72)] := by simp
  have key : ∀ x n, Outside x n (R.rt ++ R2.priv ++ [(s.sp.toNat - 4192, s.sp.toNat + 72)]) →
      Outside x n (R.rt ++ [(s.sp.toNat - 96 - 4096, s.sp.toNat - 96 - 8)]) := by
    intro x n ho
    simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at ho ⊢
    refine ⟨ho.1.1, ?_⟩
    have := ho.2
    te_omega
  have A : MemFrame s.mem (m4.writeLE (t.toNat + 8) 8 fl.toNat) (R.rt ++ R2.priv ++ [(s.sp.toNat - 4192, s.sp.toNat + 72)]) :=
    hbase.writeLE_inRanges _ f1
  have B : MemFrame s.mem m5 (R.rt ++ R2.priv ++ [(s.sp.toNat - 4192, s.sp.toNat + 72)]) :=
    A.trans hMF5 (fun x n ho => ⟨ho, key x n ho⟩)
  have C : MemFrame s.mem (CH m5 buf.toNat t.toNat fp.toNat q.toNat sl.toNat (s.mem.readLE strconvErrSyntax 8))
      (R.rt ++ R2.priv ++ [(s.sp.toNat - 4192, s.sp.toNat + 72)]) := by
    unfold CH
    exact ((((B.writeLE_inRanges _ hB5').writeLE_inRanges _ hB5'').writeLE_inRanges _ f0).writeLE_inRanges _ f2
      |>.writeLE_inRanges _ f3).writeLE_inRanges _ f4
  have D : MemFrame s.mem m6 (R.rt ++ R2.priv ++ [(s.sp.toNat - 4192, s.sp.toNat + 72)]) :=
    C.trans hMF6 (fun x n ho => ⟨ho, key x n ho⟩)
  have hFin : MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(s.sp.toNat - 4192, s.sp.toNat + 72)]) := by
    rw [hm]; unfold FM
    exact (D.writeLE_inRanges _ hB6').writeLE_inRanges _ f5
  have hsl : sl.toNat < 2 ^ 64 := sl.isLt
  have hfl : fl.toNat < 2 ^ 64 := fl.isLt
  have hfp : fp.toNat < 2 ^ 64 := fp.isLt
  have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  have e0lt : s.mem.readLE strconvErrSyntax 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt s.mem strconvErrSyntax 8
    rw [h8] at this; exact this
  have e1lt : s.mem.readLE (strconvErrSyntax + 8) 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt s.mem (strconvErrSyntax + 8) 8
    rw [h8] at this; exact this
  have hf := f_fields (buf := buf.toNat) (buf1 := buf1.toNat) hLF5 hLF6
    (⟨(t.toNat, t.toNat + 48), by simp, Nat.le_refl _, Nat.le_refl _⟩ : InRanges t.toNat 48 _)
    (by have := hAt5; simp only [Apart] at this; omega) (by have := hAL6.2; simp only [Apart] at this; omega)
    hfl hfp qlt hsl e0lt e1lt
  have hts0 := InRanges.disjoint hInT e9
  have hwin : ∀ a n, s.sp.toNat - 4192 ≤ a → a + n ≤ s.sp.toNat + 72 → Outside a n R.rt ∧ Outside a n R2.priv :=
    fun a n h1 h2 => ⟨Outside.of_sub e9 (by te_omega) (by te_omega), Outside.of_sub e10 (by te_omega) (by te_omega)⟩
  have hrec : ∀ a, (a = s.sp.toNat - 8 ∨ a = s.sp.toNat) → s'.mem.readLE a 8 = s.mem.readLE a 8 := by
    intro a ha
    have h1 : s.sp.toNat - 4192 ≤ a := by rcases ha with rfl | rfl <;> te_omega
    have h2 : a + 8 ≤ s.sp.toNat + 72 := by rcases ha with rfl | rfl <;> te_omega
    have h3 : a + 8 ≤ t.toNat ∨ t.toNat + 48 ≤ a := by rcases ha with rfl | rfl <;> te_omega
    have hB5a : a + 8 ≤ buf.toNat ∨ buf.toNat + 16 ≤ a := by
      have := (InRanges.apart hB5 (hwin a 8 h1 h2).1); simp only [Apart] at this; omega
    have hB6a : a + 8 ≤ buf1.toNat ∨ buf1.toNat + 8 ≤ a := by
      have := (InRanges.apart hB6 (hwin a 8 h1 h2).1); simp only [Apart] at this; omega
    have hs2 : a + 8 ≤ s.sp.toNat - 96 - 4096 ∨ s.sp.toNat - 96 - 8 ≤ a := by rcases ha with rfl | rfl <;> te_omega
    rw [hm]; unfold FM
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [hMF6.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨(hwin a 8 h1 h2).1, hs2⟩)]
    unfold CH
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [hMF5.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨(hwin a 8 h1 h2).1, hs2⟩)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [te0_lrS hfr hMF1 hMF2 hMF3 hdep hlow hInR hQsl _ _ (hwin a 8 h1 h2).1 (hwin a 8 h1 h2).2
      (by rcases ha with rfl | rfl <;> te_omega) (by rcases ha with rfl | rfl <;> te_omega)
      (by rcases ha with rfl | rfl <;> te_omega) (by rcases ha with rfl | rfl <;> te_omega)
      (by rcases ha with rfl | rfl <;> te_omega)]
    rcases ha with rfl | rfl
    · exact hSrec.1
    · exact hSrec.2
  refine ⟨hsp', hr29, hr28, hr18, ⟨q.toNat, t, hr0, hr1, ?_⟩, hFin, hrec _ (Or.inl rfl), hrec _ (Or.inr rfl)⟩
  unfold TeObj
  rw [hm]
  have hqw := InRanges.disjoint hInR e9
  have hApt := hApT.2
  simp only [Apart] at hqw hApt
  refine ⟨hInR, hInT, hApL, ?_, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2, ?_, ?_⟩
  · simp only [apartAll_append, apartAll_cons, apartAll_nil, and_true, b48, Nat.add_sub_cancel_left]; exact hApT
  · intro k hk
    have hsrc : (m2.writeLE (s.sp.toNat - 16) 8 q.toNat).readLE (sp.toNat + k) 1 = s.mem.readLE (sp.toNat + k) 1 := by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by te_omega)]
      rcases hspR with ho | hi
      · rw [hMF1.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          refine ⟨Outside.of_sub ho (by te_omega) (by te_omega), ?_, ?_⟩ <;> te_omega)]
        rw [hfr.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          refine ⟨Outside.of_sub hspP (by te_omega) (by te_omega), ?_, ?_⟩ <;> te_omega)]
        exact hSf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; te_omega)
      · rw [hLF1.readLE_nil _ _ (InRanges.sub hi (by te_omega) (by te_omega))]
        rw [hfr.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          refine ⟨Outside.of_sub hspP (by te_omega) (by te_omega), ?_, ?_⟩ <;> te_omega)]
        exact hSf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; te_omega)
    have hq4 : m4.readLE (q.toNat + k) 1 = s.mem.readLE (sp.toNat + k) 1 :=
      m4_copy (hLF := hLF3) hk hQsl (by te_omega) (by te_omega) hCop hsrc
    rw [f_q (buf := buf.toNat) (buf1 := buf1.toNat) hLF5 hLF6
      (⟨(q.toNat, q.toNat + blockSize sl.toNat true), by simp, Nat.le_refl _, Nat.le_refl _⟩ : InRanges q.toNat _ _)
      (Nat.lt_of_lt_of_le hk hQsl) (by have := hAq5; simp only [Apart] at this; omega)
      (by have := hAL6.1.2; simp only [Apart] at this; omega) hApt]
    exact hq4
  · have hl : L ++ [(q.toNat, q.toNat + blockSize sl.toNat true), (t.toNat, t.toNat + blockSize 48 false)] =
        L ++ [(q.toNat, q.toNat + blockSize sl.toNat true)] ++ [(t.toNat, t.toNat + 48)] := by simp [b48]
    rw [hl]
    unfold FM
    rw [view_writeLE_live (⟨(t.toNat, t.toNat + 48), by simp, by omega, by omega⟩ : InRanges (t.toNat + 40) 8 _)]
    rw [b48]
    exact Fv256.Amd64.SfdToError.inv_slot1 hIS6 hB6
      (Fv256.Amd64.SfdToError.outside_of_apart3 hAL6.1.1 hAL6.1.2 hAL6.2)

end Fv256.Arm64.SfdToError
