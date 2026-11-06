import Fv256.Spec
import Fv256.Util
import Fv256.Arm64.SfdTeTail0

/-!
# `strconv.toError` (arm64): memory-frame lemmas of the `ErrSyntax` path (extraction-free)
-/

open Janus Janus.Contracts Janus.Spec

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

end Fv256.Arm64.SfdToError
