import Fv256.Spec
import Fv256.Util
import Fv256.Arm64.SfdTeTail0

/-!
# `strconv.toError` (arm64): memory-frame lemmas of the `ErrSyntax` path (extraction-free)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.Arm64.SfdEnv

namespace Fv256.Arm64.SfdToError

/-- `omega` after dropping the hypotheses unrelated to the goal (the contexts carry giant memory terms) -/
macro "te_omega" : tactic => `(tactic| first | (janus_clear_irrel; omega) | omega)

set_option maxRecDepth 20000 in
/-- the memory frame of the flag-0 `ErrSyntax` path up to the stores into the fresh `NumError`: the entry stores, the
`ifaceeq`, `mallocgc`, `memmove` and `newobject` frames, all inside `rt ++ priv ++ [window]` -/
theorem te0_base {m0 S m' m2 m3 m4 : Janus.Arm64.Memory} {rt priv : List (Nat × Nat)}
    {r4 depth q bs sl qv x1 x2 : Nat}
    (hSf : MemFrame m0 S [(r4 - (depth + 96), r4 + 72)])
    (hfr : MemFrame S m' (priv ++ [(r4 - 96 - depth, r4 - 96 - 8), (r4 - 96 + 8, r4 - 96 + 8 + 24)]))
    (hMF1 : MemFrame m' m2 (rt ++ [(r4 - 96 - 4096, r4 - 96 - 8), (r4 - 96 + 8, r4 - 96 + 8 + 24)]))
    (hMF2 : MemFrame (m2.writeLE (r4 - 16) 8 qv) m3
      (rt ++ [(r4 - 96 - 4096, r4 - 96 - 8), (r4 - 96 + 8, r4 - 96 + 8 + 24)] ++ [(q, q + sl)]))
    (hMF3 : MemFrame ((m3.writeLE (r4 - 40) 8 x1).writeLE (r4 - 24) 8 x2) m4
      (rt ++ [(r4 - 96 - 4096, r4 - 96 - 8), (r4 - 96 + 8, r4 - 96 + 8 + 8)]))
    (hdep : depth ≤ 4096) (hr4 : 4192 ≤ r4) (hq : InRanges q bs rt) (hsl : sl ≤ bs) :
    MemFrame m0 m4 (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) := by
  have hW : (r4 - 4192, r4 + 72) ∈ rt ++ priv ++ [(r4 - 4192, r4 + 72)] := by simp
  have key : ∀ x n, Outside x n (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) →
      Outside x n rt ∧ Outside x n priv ∧ (x + n ≤ r4 - 4192 ∨ r4 + 72 ≤ x) := by
    intro x n ho
    simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at ho
    exact ⟨ho.1.1, ho.1.2, ho.2⟩
  have A : MemFrame m0 S (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) :=
    hSf.mono (fun x n ho => by
      obtain ⟨_, _, h3⟩ := key x n ho
      simp only [Janus.outside_cons, Janus.outside_nil, and_true]; omega)
  have B : MemFrame m0 m' (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) := by
    refine A.trans hfr (fun x n ho => ⟨ho, ?_⟩)
    obtain ⟨_, h2, h3⟩ := key x n ho
    simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    refine ⟨h2, ?_, ?_⟩ <;> omega
  have C : MemFrame m0 m2 (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) := by
    refine B.trans hMF1 (fun x n ho => ⟨ho, ?_⟩)
    obtain ⟨h1, _, h3⟩ := key x n ho
    simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    refine ⟨h1, ?_, ?_⟩ <;> omega
  have C' : MemFrame m0 (m2.writeLE (r4 - 16) 8 qv) (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) :=
    C.writeLE _ hW (by omega) (by omega)
  have D : MemFrame m0 m3 (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) := by
    refine C'.trans hMF2 (fun x n ho => ⟨ho, ?_⟩)
    obtain ⟨h1, _, h3⟩ := key x n ho
    have hap := InRanges.apart hq h1
    simp only [Apart] at hap
    simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    refine ⟨⟨h1, ?_, ?_⟩, ?_⟩ <;> omega
  have D' : MemFrame m0 ((m3.writeLE (r4 - 40) 8 x1).writeLE (r4 - 24) 8 x2) (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) :=
    (D.writeLE _ hW (by omega) (by omega)).writeLE _ hW (by omega) (by omega)
  refine D'.trans hMF3 (fun x n ho => ⟨ho, ?_⟩)
  obtain ⟨h1, _, h3⟩ := key x n ho
  simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
  refine ⟨h1, ?_, ?_⟩ <;> omega

/-- the fields of the finished object, read back from `TailMem` -/
theorem tm_fields (m : Janus.Arm64.Memory) (t fl q sl e0 e1 fn : Nat)
    (hfl : fl < 2 ^ 64) (hq : q < 2 ^ 64) (hsl : sl < 2 ^ 64) (he0 : e0 < 2 ^ 64) (he1 : e1 < 2 ^ 64) (hfn : fn < 2 ^ 64) :
    (TailMem m t fl q sl e0 e1 fn).readLE t 8 = fn ∧ (TailMem m t fl q sl e0 e1 fn).readLE (t + 8) 8 = fl ∧
    (TailMem m t fl q sl e0 e1 fn).readLE (t + 16) 8 = q ∧ (TailMem m t fl q sl e0 e1 fn).readLE (t + 24) 8 = sl ∧
    (TailMem m t fl q sl e0 e1 fn).readLE (t + 32) 8 = e0 ∧ (TailMem m t fl q sl e0 e1 fn).readLE (t + 40) 8 = e1 := by
  have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  unfold TailMem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]; rw [h8]; exact Nat.mod_eq_of_lt (by assumption))

/-- the view of the live set is unchanged by the six stores into the fresh object -/
theorem tm_view {rt L : List (Nat × Nat)} {m : Janus.Arm64.Memory} {t fl q sl e0 e1 fn : Nat}
    (ht : InRanges t 48 L) :
    view rt L (TailMem m t fl q sl e0 e1 fn) = view rt L m := by
  have h : ∀ k, k + 8 ≤ 48 → InRanges (t + k) 8 L := fun k hk => by
    obtain ⟨r, hr, h1, h2⟩ := ht; exact ⟨r, hr, by omega, by omega⟩
  unfold TailMem
  rw [view_writeLE_live (h 40 (by omega)), view_writeLE_live (h 32 (by omega)), view_writeLE_live (h 24 (by omega)),
    view_writeLE_live (h 16 (by omega)), view_writeLE_live (by simpa using h 0 (by omega)), view_writeLE_live (h 8 (by omega))]

/-- the copied string `q`, read back through the stores into the fresh object and the `newobject` frame -/
theorem te0_copy {m3 m4 M0 : Janus.Arm64.Memory} {L : List (Nat × Nat)} {fl q' sl' e0 e1 fn v1 v2 : Nat}
    {t q bs sl sp k a1 a2 X : Nat}
    (hLF : LiveFrame ((m3.writeLE a1 8 v1).writeLE a2 8 v2) m4 (L ++ [(q, q + bs)]) [])
    (hApt : t + 48 ≤ q ∨ q + bs ≤ t) (hk : k < sl) (hsl : sl ≤ bs)
    (hd1 : q + k + 1 ≤ a1 ∨ a1 + 8 ≤ q + k) (hd2 : q + k + 1 ≤ a2 ∨ a2 + 8 ≤ q + k)
    (hCop : Mem.Copied M0 m3 q sp sl) (hsrc : M0.readLE (sp + k) 1 = X) :
    (TailMem m4 t fl q' sl' e0 e1 fn).readLE (q + k) 1 = X := by
  unfold TailMem
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  rw [hLF.readLE_nil _ _ ⟨(q, q + bs), by simp, by omega, by omega⟩]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  rw [Janus.Arm64.Memory.readLE_one, hCop k hk, ← Janus.Arm64.Memory.readLE_one]
  exact hsrc

/-- the frame of the finished object: the stores into `t` stay inside `rt` -/
theorem tm_frame {m0 m4 : Janus.Arm64.Memory} {Lst rt : List (Nat × Nat)} {t fl q sl e0 e1 fn : Nat}
    (hF : MemFrame m0 m4 Lst) (hsub : ∀ r ∈ rt, r ∈ Lst) (ht : InRanges t 48 rt) :
    MemFrame m0 (TailMem m4 t fl q sl e0 e1 fn) Lst := by
  have h : ∀ k, k + 8 ≤ 48 → InRanges (t + k) 8 Lst := fun k hk => by
    obtain ⟨r, hr, h1, h2⟩ := ht; exact ⟨r, hsub r hr, by omega, by omega⟩
  unfold TailMem
  exact (((((hF.writeLE_inRanges _ (h 8 (by omega))).writeLE_inRanges _ (by simpa using h 0 (by omega))).writeLE_inRanges _ (h 16 (by omega))).writeLE_inRanges _ (h 24 (by omega))).writeLE_inRanges _ (h 32 (by omega))).writeLE_inRanges _ (h 40 (by omega))

theorem rr_mono {p : Program} {ret : BitVec 64} {S : State} {Q Q' : State → Prop}
    (h : ReachesRet p ret S Q) (hQ : ∀ s', Q s' → Q' s') : ReachesRet p ret S Q' := by
  obtain ⟨k, s', a, b, c⟩ := h
  exact ⟨k, s', a, b, hQ _ c⟩

/-- reads of an address outside everything the `toError` path writes see the memory `S` at the `ifaceeq` call -/
theorem te0_lrS {S m' m2 m3 m4 : Janus.Arm64.Memory} {rt priv : List (Nat × Nat)} {r4 depth q bs sl qv x1 x2 : Nat}
    (hfr : MemFrame S m' (priv ++ [(r4 - 96 - depth, r4 - 96 - 8), (r4 - 96 + 8, r4 - 96 + 8 + 24)]))
    (hMF1 : MemFrame m' m2 (rt ++ [(r4 - 96 - 4096, r4 - 96 - 8), (r4 - 96 + 8, r4 - 96 + 8 + 24)]))
    (hMF2 : MemFrame (m2.writeLE (r4 - 16) 8 qv) m3
      (rt ++ [(r4 - 96 - 4096, r4 - 96 - 8), (r4 - 96 + 8, r4 - 96 + 8 + 24)] ++ [(q, q + sl)]))
    (hMF3 : MemFrame ((m3.writeLE (r4 - 40) 8 x1).writeLE (r4 - 24) 8 x2) m4
      (rt ++ [(r4 - 96 - 4096, r4 - 96 - 8), (r4 - 96 + 8, r4 - 96 + 8 + 8)]))
    (hdep : depth ≤ 4096) (hr4 : 4192 ≤ r4) (hInR : InRanges q bs rt) (hQsl : sl ≤ bs) (a n : Nat)
    (h1 : Outside a n rt) (h2 : Outside a n priv)
    (d1 : a + n ≤ r4 - 96 - 4096 ∨ r4 - 96 - 8 ≤ a) (d2 : a + n ≤ r4 - 96 + 8 ∨ r4 - 96 + 8 + 24 ≤ a)
    (d3 : a + n ≤ r4 - 40 ∨ r4 - 32 ≤ a) (d4 : a + n ≤ r4 - 24 ∨ r4 - 16 ≤ a) (d5 : a + n ≤ r4 - 16 ∨ r4 - 8 ≤ a) :
    m4.readLE a n = S.readLE a n := by
  have hq := InRanges.disjoint hInR h1
  rw [hMF3.readLE _ _ (by
        simp only [calleeStack, outside_append, outside_cons, outside_nil, and_true]
        (repeat' apply And.intro) <;> first | exact h1 | omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      hMF2.readLE _ _ (by
        simp only [calleeStack, outside_append, outside_cons, outside_nil, and_true]
        (repeat' apply And.intro) <;> first | exact h1 | omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      hMF1.readLE _ _ (by
        simp only [calleeStack, outside_append, outside_cons, outside_nil, and_true]
        (repeat' apply And.intro) <;> first | exact h1 | omega),
      hfr.readLE _ _ (by
        simp only [calleeStack, outside_append, outside_cons, outside_nil, and_true]
        (repeat' apply And.intro) <;> first | exact h2 | omega)]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- the `TePost` of the flag-0 `ErrSyntax` path from the tail's postcondition and the frames of the prefix -/
theorem te0_conv {R : RtInv} {R2 : IfaceModel} {b : Nat} {L : List (Nat × Nat)} {fp fl sp sl : BitVec 64}
    {s S St s' : State} {m' m2 m3 m4 : Janus.Arm64.Memory} {q t : BitVec 64}
    (hdep : R2.depth ≤ 4096) (hlow : 4192 ≤ s.sp.toNat)
    (e9 : Outside (s.sp.toNat - 4192) (s.sp.toNat + 72 - (s.sp.toNat - 4192)) R.rt)
    (e10 : Outside (s.sp.toNat - 4192) (s.sp.toNat + 72 - (s.sp.toNat - 4192)) R2.priv)
    (hSf : MemFrame s.mem S.mem [(s.sp.toNat - (R2.depth + 96), s.sp.toNat + 72)])
    (hfr : MemFrame S.mem m' (R2.priv ++ [(s.sp.toNat - 96 - R2.depth, s.sp.toNat - 96 - 8),
      (s.sp.toNat - 96 + 8, s.sp.toNat - 96 + 8 + 24)]))
    (hMF1 : MemFrame m' m2 (R.rt ++ [(s.sp.toNat - 96 - 4096, s.sp.toNat - 96 - 8), (s.sp.toNat - 96 + 8, s.sp.toNat - 96 + 8 + 24)]))
    (hMF2 : MemFrame (m2.writeLE (s.sp.toNat - 16) 8 q.toNat) m3
      (R.rt ++ [(s.sp.toNat - 96 - 4096, s.sp.toNat - 96 - 8), (s.sp.toNat - 96 + 8, s.sp.toNat - 96 + 8 + 24)] ++
        [(q.toNat, q.toNat + sl.toNat)]))
    (hMF3 : MemFrame ((m3.writeLE (s.sp.toNat - 40) 8 sl.toNat).writeLE (s.sp.toNat - 24) 8 q.toNat) m4
      (R.rt ++ [(s.sp.toNat - 96 - 4096, s.sp.toNat - 96 - 8), (s.sp.toNat - 96 + 8, s.sp.toNat - 96 + 8 + 8)]))
    (hLF1 : LiveFrame m' m2 L [])
    (hLF3 : LiveFrame ((m3.writeLE (s.sp.toNat - 40) 8 sl.toNat).writeLE (s.sp.toNat - 24) 8 q.toNat) m4
      (L ++ [(q.toNat, q.toNat + blockSize sl.toNat true)]) [])
    (hCop : Mem.Copied (m2.writeLE (s.sp.toNat - 16) 8 q.toNat) m3 q.toNat sp.toNat sl.toNat)
    (hinvN : R.inv (b - blockSize sl.toNat true - 48)
      (L ++ [(q.toNat, q.toNat + blockSize sl.toNat true)] ++ [(t.toNat, t.toNat + 48)]) (s.regs 28).toNat
      (view R.rt (L ++ [(q.toNat, q.toNat + blockSize sl.toNat true)] ++ [(t.toNat, t.toNat + 48)]) m4))
    (hInR : InRanges q.toNat (blockSize sl.toNat true) R.rt) (hInT : InRanges t.toNat (blockSize 48 false) R.rt)
    (hApL : ApartAll q.toNat (blockSize sl.toNat true) L)
    (hApT : ApartAll t.toNat 48 L ∧ Apart t.toNat 48 q.toNat (blockSize sl.toNat true))
    (hQsl : sl.toNat ≤ blockSize sl.toNat true)
    (hspR : Outside sp.toNat sl.toNat R.rt ∨ InRanges sp.toNat sl.toNat L) (hspP : Outside sp.toNat sl.toNat R2.priv)
    (hsdisj : sp.toNat + sl.toNat ≤ s.sp.toNat - 4192 ∨ s.sp.toNat + 72 ≤ sp.toNat)
    (hSm8 : S.mem.readLE (s.sp.toNat + 8) 8 = fp.toNat)
    (oE : Outside strconvErrSyntax 16 [(s.sp.toNat - 4192, s.sp.toNat + 72)])
    (pE : Outside strconvErrSyntax 16 R.rt) (qE : Outside strconvErrSyntax 16 R2.priv)
    (hSrec : S.mem.readLE (s.sp.toNat - 8) 8 = s.mem.readLE (s.sp.toNat - 8) 8 ∧
      S.mem.readLE s.sp.toNat 8 = s.mem.readLE s.sp.toNat 8)
    (hSp : St.sp = s.sp - 96#64) (hSt28 : St.regs 28 = s.regs 28) (hSt18 : St.regs 18 = s.regs 18)
    (htail : s'.sp = St.sp + 96#64 ∧ s'.regs 0 = BitVec.ofNat 64 numErrItab ∧ s'.regs 1 = t ∧ s'.regs 29 = s.regs 29 ∧
      s'.regs 28 = St.regs 28 ∧ s'.regs 18 = St.regs 18 ∧
      s'.mem = TailMem m4 t.toNat fl.toNat (m4.readLE (St.sp.toNat + 72) 8) (m4.readLE (St.sp.toNat + 56) 8)
        (m4.readLE strconvErrSyntax 8) (m4.readLE (strconvErrSyntax + 8) 8) (m4.readLE (St.sp.toNat + 104) 8)) :
    TePost R R2 b L fp fl sp sl s s' := by
  obtain ⟨hsp', hr0, hr1, hr29, hr28, hr18, hmem'⟩ := htail
  have hsp0 : St.sp.toNat = s.sp.toNat - 96 := by
    rw [hSp, BitVec.toNat_sub]; simp; omega
  rw [hsp0] at hmem'
  have hwin : ∀ a n, s.sp.toNat - 4192 ≤ a → a + n ≤ s.sp.toNat + 72 → Outside a n R.rt ∧ Outside a n R2.priv :=
    fun a n h1 h2 => ⟨Outside.of_sub e9 (by te_omega) (by te_omega), Outside.of_sub e10 (by te_omega) (by te_omega)⟩
  have b48 : blockSize 48 false = 48 := by decide
  have qlt : q.toNat < 2 ^ 64 := q.isLt
  have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  have hq4 : m4.readLE (s.sp.toNat - 24) 8 = q.toNat := by
    rw [hMF3.readLE _ _ (by
          simp only [calleeStack, outside_append, outside_cons, outside_nil, and_true]
          (repeat' apply And.intro) <;> first | exact (hwin _ _ (by te_omega) (by te_omega)).1 | te_omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
    rw [h8]; exact Nat.mod_eq_of_lt qlt
  have hsl4 : m4.readLE (s.sp.toNat - 40) 8 = sl.toNat := by
    rw [hMF3.readLE _ _ (by
          simp only [calleeStack, outside_append, outside_cons, outside_nil, and_true]
          (repeat' apply And.intro) <;> first | exact (hwin _ _ (by te_omega) (by te_omega)).1 | te_omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [h8]; exact Nat.mod_eq_of_lt sl.isLt
  have hfn4 : m4.readLE (s.sp.toNat + 8) 8 = fp.toNat := by
    rw [te0_lrS hfr hMF1 hMF2 hMF3 hdep hlow hInR hQsl _ _ (hwin _ _ (by te_omega) (by te_omega)).1
      (hwin _ _ (by te_omega) (by te_omega)).2 (by te_omega) (by te_omega) (by te_omega) (by te_omega) (by te_omega)]
    exact hSm8
  have he0 : ∀ a, (a = strconvErrSyntax ∨ a = strconvErrSyntax + 8) → m4.readLE a 8 = s.mem.readLE a 8 := by
    intro a ha
    have hao : Outside a 8 [(s.sp.toNat - 4192, s.sp.toNat + 72)] := by
      rcases ha with rfl | rfl <;> exact Outside.of_sub oE (by te_omega) (by te_omega)
    have hap : Outside a 8 R.rt := by
      rcases ha with rfl | rfl <;> exact Outside.of_sub pE (by te_omega) (by te_omega)
    have hapr : Outside a 8 R2.priv := by
      rcases ha with rfl | rfl <;> exact Outside.of_sub qE (by te_omega) (by te_omega)
    simp only [outside_cons, outside_nil, and_true] at hao
    rw [te0_lrS hfr hMF1 hMF2 hMF3 hdep hlow hInR hQsl _ _ hap hapr (by te_omega) (by te_omega) (by te_omega)
      (by te_omega) (by te_omega)]
    exact hSf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; te_omega)
  have e0lt : s.mem.readLE strconvErrSyntax 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt s.mem strconvErrSyntax 8
    rw [h8] at this; exact this
  have e1lt : s.mem.readLE (strconvErrSyntax + 8) 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt s.mem (strconvErrSyntax + 8) 8
    rw [h8] at this; exact this
  have a72 : s.sp.toNat - 96 + 72 = s.sp.toNat - 24 := by omega
  have a56 : s.sp.toNat - 96 + 56 = s.sp.toNat - 40 := by omega
  have a104 : s.sp.toNat - 96 + 104 = s.sp.toNat + 8 := by omega
  rw [a72, a56, a104, hq4, hsl4, hfn4, he0 _ (Or.inl rfl), he0 _ (Or.inr rfl)] at hmem'
  have hf := tm_fields m4 t.toNat fl.toNat q.toNat sl.toNat (s.mem.readLE strconvErrSyntax 8)
    (s.mem.readLE (strconvErrSyntax + 8) 8) fp.toNat fl.isLt qlt sl.isLt e0lt e1lt fp.isLt
  have hbase := te0_base hSf hfr hMF1 hMF2 hMF3 hdep hlow hInR hQsl
  have hFin : MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(s.sp.toNat - 4192, s.sp.toNat + 72)]) := by
    rw [hmem']; exact tm_frame hbase (fun r hr => by simp [hr]) hInT
  have hts0 := InRanges.disjoint hInT e9
  rw [b48] at hts0
  have hrec : ∀ a, (a = s.sp.toNat - 8 ∨ a = s.sp.toNat) → s'.mem.readLE a 8 = s.mem.readLE a 8 := by
    intro a ha
    have h1 : s.sp.toNat - 4192 ≤ a := by rcases ha with rfl | rfl <;> te_omega
    have h2 : a + 8 ≤ s.sp.toNat + 72 := by rcases ha with rfl | rfl <;> te_omega
    have h3 : a + 8 ≤ t.toNat ∨ t.toNat + 48 ≤ a := by rcases ha with rfl | rfl <;> te_omega
    rw [hmem']
    unfold TailMem
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [te0_lrS hfr hMF1 hMF2 hMF3 hdep hlow hInR hQsl _ _ (hwin _ _ h1 h2).1 (hwin _ _ h1 h2).2
      (by rcases ha with rfl | rfl <;> te_omega) (by rcases ha with rfl | rfl <;> te_omega)
      (by rcases ha with rfl | rfl <;> te_omega) (by rcases ha with rfl | rfl <;> te_omega)
      (by rcases ha with rfl | rfl <;> te_omega)]
    rcases ha with rfl | rfl
    · exact hSrec.1
    · exact hSrec.2
  refine ⟨?_, hr29, ?_, ?_, ⟨q.toNat, t, hr0, hr1, ?_⟩, hFin, hrec _ (Or.inl rfl), hrec _ (Or.inr rfl)⟩
  · rw [hsp', hSp]; bv_omega
  · rw [hr28, hSt28]
  · rw [hr18, hSt18]
  · unfold TeObj
    rw [hmem']
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
      exact te0_copy (hLF := hLF3) (hApt := hApt) hk hQsl (by te_omega) (by te_omega) hCop hsrc
    · have hl : L ++ [(q.toNat, q.toNat + blockSize sl.toNat true), (t.toNat, t.toNat + blockSize 48 false)] =
          L ++ [(q.toNat, q.toNat + blockSize sl.toNat true)] ++ [(t.toNat, t.toNat + 48)] := by simp [b48]
      rw [hl, tm_view (rt := R.rt) ⟨(t.toNat, t.toNat + 48), by simp, Nat.le_refl _, Nat.le_refl _⟩]
      rw [b48]; exact hinvN

end Fv256.Arm64.SfdToError
