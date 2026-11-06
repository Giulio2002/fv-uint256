import Fv256.SumC64

/-!
# Memory-chain lemmas for the `strconv.toError` summary (amd64)

Light, extraction-free lemmas about the memory terms the `ErrSyntax` branch of `strconv.toError` produces, so that
the long `te_sum` proof does not have to walk the store chains with `simp` (it exhausts memory on the big contexts).
-/

open Janus Janus.Contracts

namespace Fv256.Amd64.SfdToError

theorem inRanges_fields {t : Nat} {rs rs' : List (Nat × Nat)} (h : InRanges t 48 rs) (hs : ∀ r ∈ rs, r ∈ rs') :
    InRanges t 8 rs' ∧ InRanges (t + 8) 8 rs' ∧ InRanges (t + 16) 8 rs' ∧ InRanges (t + 24) 8 rs' ∧
      InRanges (t + 32) 8 rs' ∧ InRanges (t + 40) 8 rs' := by
  obtain ⟨r, hr, h1, h2⟩ := h
  have hr' := hs r hr
  exact ⟨⟨r, hr', by omega, by omega⟩, ⟨r, hr', by omega, by omega⟩, ⟨r, hr', by omega, by omega⟩,
    ⟨r, hr', by omega, by omega⟩, ⟨r, hr', by omega, by omega⟩, ⟨r, hr', by omega, by omega⟩⟩

theorem frame_trans {m m' m'' : Janus.Arm64.Memory} {rs rs' : List (Nat × Nat)} (h : MemFrame m m' rs)
    (h' : MemFrame m' m'' rs') (sub : ∀ a n, Outside a n rs → Outside a n rs') : MemFrame m m'' rs :=
  h.trans h' (fun a n ho => ⟨ho, sub a n ho⟩)

theorem inRanges16_lo {a : Nat} {rs : List (Nat × Nat)} (h : InRanges a 16 rs) : InRanges a 8 rs := by
  obtain ⟨r, hr, h1, h2⟩ := h; exact ⟨r, hr, by omega, by omega⟩

theorem inRanges16_hi {a : Nat} {rs : List (Nat × Nat)} (h : InRanges a 16 rs) : InRanges (a + 8) 8 rs := by
  obtain ⟨r, hr, h1, h2⟩ := h; exact ⟨r, hr, by omega, by omega⟩

theorem frame_writeLE_rt {m m' : Janus.Arm64.Memory} {rt priv : List (Nat × Nat)} {w : Nat × Nat} {a k : Nat} (v : Nat)
    (h : MemFrame m m' (rt ++ priv ++ [w])) (hin : InRanges a k rt) :
    MemFrame m (m'.writeLE a k v) (rt ++ priv ++ [w]) :=
  h.writeLE_inRanges v (InRanges.of_subset hin (by intro r hr; simp [List.mem_append, hr]))

/-- the bytes copied into the fresh string `q`, read back through the stores into the fresh `NumError` `t` and
through the `newobject` call -/
theorem te_copy {M w2 w10 M0 : Janus.Arm64.Memory} {L : List (Nat × Nat)}
    {t q bs sl sp k a1 a2 a3 v1 v2 v3 x1 x2 x3 x4 x5 x6 X : Nat}
    (hM : M = (((((w2.writeLE (t + 8) 8 x1).writeLE t 8 x2).writeLE (t + 24) 8 x3).writeLE (t + 16) 8 x4).writeLE
      (t + 32) 8 x5).writeLE (t + 40) 8 x6)
    (hLF : LiveFrame (((w10.writeLE a1 8 v1).writeLE a2 8 v2).writeLE a3 8 v3) w2 (L ++ [(q, q + bs)]) [])
    (hApt : t + 48 ≤ q ∨ q + bs ≤ t) (hk : k < sl) (hsl : sl ≤ bs)
    (hd1 : q + k + 1 ≤ a1 ∨ a1 + 8 ≤ q + k) (hd2 : q + k + 1 ≤ a2 ∨ a2 + 8 ≤ q + k)
    (hd3 : q + k + 1 ≤ a3 ∨ a3 + 8 ≤ q + k)
    (hCop : Mem.Copied M0 w10 q sp sl) (hsrc : M0.readLE (sp + k) 1 = X) :
    M.readLE (q + k) 1 = X := by
  subst hM
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  rw [hLF.readLE_nil _ _ ⟨(q, q + bs), by simp, by omega, by omega⟩]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  rw [Janus.Arm64.Memory.readLE_one, hCop k hk, ← Janus.Arm64.Memory.readLE_one]
  exact hsrc

/-- the source string, read back through the callee-stack stores and the `mallocgc` frame -/
theorem te_src {m' m2 : Janus.Arm64.Memory} {L rt : List (Nat × Nat)} {r4 sp sl k c qv c2 X : Nat}
    (hLF : LiveFrame (m'.writeLE (r4 - 96) 8 c) m2 L [])
    (hMF : MemFrame (m'.writeLE (r4 - 96) 8 c) m2 (rt ++ [(r4 - 96 - 4096, r4 - 96), (r4 - 96 + 8, r4 - 96 + 8 + 24)]))
    (hspR : Outside sp sl rt ∨ InRanges sp sl L) (hk : k < sl) (hw : sp + sl ≤ r4 - 4192 ∨ r4 + 72 ≤ sp)
    (hm' : m'.readLE (sp + k) 1 = X) :
    ((m2.writeLE (r4 - 16) 8 qv).writeLE (r4 - 96) 8 c2).readLE (sp + k) 1 = X := by
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  rcases hspR with ho | hi
  · rw [hMF.readLE _ _ (by
      simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
      refine ⟨Outside.of_sub ho (by omega) (by omega), ?_, ?_⟩ <;> omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    exact hm'
  · rw [hLF.readLE_nil _ _ (InRanges.sub hi (by omega) (by omega))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    exact hm'

/-- the source string, read back through the `ifaceeq` call's frame and the caller's stack stores -/
theorem te_hfr {s0 m' : Janus.Arm64.Memory} {priv : List (Nat × Nat)} {r4 sp sl k depth a b c d e f g h i j : Nat}
    (hfr : MemFrame ((((((((((s0.writeLE (r4 - 8) 8 a).writeLE (r4 + 40) 8 b).writeLE (r4 + 48) 8 c).writeLE
      (r4 + 64) 8 d).writeLE (r4 + 56) 8 e).writeLE (r4 + 32) 8 f).writeLE (r4 + 24) 8 g).writeLE (r4 + 8) 8 h).writeLE
      (r4 + 16) 8 i).writeLE (r4 - 96) 8 j) m'
      (priv ++ [(r4 - 96 - depth, r4 - 96), (r4 - 96 + 8, r4 - 96 + 8 + 24)]))
    (hspP : Outside sp sl priv) (hk : k < sl) (hdep : depth ≤ 4096) (hw : sp + sl ≤ r4 - 4192 ∨ r4 + 72 ≤ sp) :
    m'.readLE (sp + k) 1 = s0.readLE (sp + k) 1 := by
  rw [hfr.readLE _ _ (by
    simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    refine ⟨Outside.of_sub hspP (by omega) (by omega), ?_, ?_⟩ <;> omega)]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]


set_option maxRecDepth 20000 in
/-- the memory frame of the `ErrSyntax` path of `strconv.toError` up to the `newobject` call (before the stores into
the fresh `NumError`): the caller's stack stores, the `ifaceeq`, `mallocgc`, `memmove` and `newobject` frames, all
inside `rt ++ priv ++ [window]` -/
theorem te_base {m0 m' m2 w10 w2 : Janus.Arm64.Memory} {rt priv : List (Nat × Nat)}
    {r4 depth q bs sl a b c d e f g h i j c1 qv c2 x1 x2 c3 : Nat}
    (hfr : MemFrame ((((((((((m0.writeLE (r4 - 8) 8 a).writeLE (r4 + 40) 8 b).writeLE (r4 + 48) 8 c).writeLE
      (r4 + 64) 8 d).writeLE (r4 + 56) 8 e).writeLE (r4 + 32) 8 f).writeLE (r4 + 24) 8 g).writeLE (r4 + 8) 8 h).writeLE
      (r4 + 16) 8 i).writeLE (r4 - 96) 8 j) m'
      (priv ++ [(r4 - 96 - depth, r4 - 96), (r4 - 96 + 8, r4 - 96 + 8 + 24)]))
    (hMF : MemFrame (m'.writeLE (r4 - 96) 8 c1) m2
      (rt ++ [(r4 - 96 - 4096, r4 - 96), (r4 - 96 + 8, r4 - 96 + 8 + 24)]))
    (hmv : MemFrame ((m2.writeLE (r4 - 16) 8 qv).writeLE (r4 - 96) 8 c2) w10
      (rt ++ [(r4 - 96 - 4096, r4 - 96), (r4 - 96 + 8, r4 - 96 + 8 + 24)] ++ [(q, q + sl)]))
    (hno : MemFrame (((w10.writeLE (r4 - 40) 8 x1).writeLE (r4 - 24) 8 x2).writeLE (r4 - 96) 8 c3) w2
      (rt ++ [(r4 - 96 - 4096, r4 - 96), (r4 - 96 + 8, r4 - 96 + 8 + 8)]))
    (hdep : depth ≤ 4096) (hr4 : 4192 ≤ r4) (hq : InRanges q bs rt) (hsl : sl ≤ bs) :
    MemFrame m0 w2 (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) := by
  have hW : (r4 - 4192, r4 + 72) ∈ rt ++ priv ++ [(r4 - 4192, r4 + 72)] := by simp
  -- unfold the target's "outside" into its three parts
  have key : ∀ x n, Outside x n (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) →
      Outside x n rt ∧ Outside x n priv ∧ (x + n ≤ r4 - 4192 ∨ r4 + 72 ≤ x) := by
    intro x n ho
    simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at ho
    exact ⟨ho.1.1, ho.1.2, ho.2⟩
  have A : MemFrame m0 ((((((((((m0.writeLE (r4 - 8) 8 a).writeLE (r4 + 40) 8 b).writeLE (r4 + 48) 8 c).writeLE
      (r4 + 64) 8 d).writeLE (r4 + 56) 8 e).writeLE (r4 + 32) 8 f).writeLE (r4 + 24) 8 g).writeLE (r4 + 8) 8 h).writeLE
      (r4 + 16) 8 i).writeLE (r4 - 96) 8 j) (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) := by
    refine ((((((((((MemFrame.refl m0 _).writeLE a hW (by omega) (by omega)).writeLE _ hW (by omega) (by omega)).writeLE _ hW
      (by omega) (by omega)).writeLE _ hW (by omega) (by omega)).writeLE _ hW (by omega) (by omega)).writeLE _ hW
      (by omega) (by omega)).writeLE _ hW (by omega) (by omega)).writeLE _ hW (by omega) (by omega)).writeLE _ hW
      (by omega) (by omega)).writeLE _ hW (by omega) (by omega)
  have B : MemFrame m0 m' (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) := by
    refine A.trans hfr (fun x n ho => ⟨ho, ?_⟩)
    obtain ⟨_, h2, h3⟩ := key x n ho
    have h2' := h2
    simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    refine ⟨h2, ?_, ?_⟩ <;> omega
  have B' : MemFrame m0 (m'.writeLE (r4 - 96) 8 c1) (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) :=
    B.writeLE _ hW (by omega) (by omega)
  have C : MemFrame m0 m2 (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) := by
    refine B'.trans hMF (fun x n ho => ⟨ho, ?_⟩)
    obtain ⟨h1, _, h3⟩ := key x n ho
    simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    refine ⟨h1, ?_, ?_⟩ <;> omega
  have C' : MemFrame m0 ((m2.writeLE (r4 - 16) 8 qv).writeLE (r4 - 96) 8 c2) (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) :=
    (C.writeLE _ hW (by omega) (by omega)).writeLE _ hW (by omega) (by omega)
  have D : MemFrame m0 w10 (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) := by
    refine C'.trans hmv (fun x n ho => ⟨ho, ?_⟩)
    obtain ⟨h1, _, h3⟩ := key x n ho
    have hap := InRanges.apart hq h1
    simp only [Apart] at hap
    simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    refine ⟨⟨h1, ?_, ?_⟩, ?_⟩ <;> omega
  have D' : MemFrame m0 (((w10.writeLE (r4 - 40) 8 x1).writeLE (r4 - 24) 8 x2).writeLE (r4 - 96) 8 c3)
      (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) :=
    ((D.writeLE _ hW (by omega) (by omega)).writeLE _ hW (by omega) (by omega)).writeLE _ hW (by omega) (by omega)
  refine D'.trans hno (fun x n ho => ⟨ho, ?_⟩)
  obtain ⟨h1, _, h3⟩ := key x n ho
  simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
  refine ⟨h1, ?_, ?_⟩ <;> omega


set_option maxRecDepth 20000 in
/-- the write-barrier branch of the `ErrSyntax` path: after the `newobject` frame (`te_base`), the first barrier
(`gcWriteBarrier2`, slot `s2` of 16 bytes inside `rt`), the stores into the slot and into the fresh `NumError` `t`, and the
second barrier (`gcWriteBarrier1`, slot `s1` of 8 bytes inside `rt`) -/
theorem te_base1 {m0 w16 w9 w2 : Janus.Arm64.Memory} {rt priv : List (Nat × Nat)}
    {r4 t s2 q a b c d e f g c4 : Nat}
    (hB : MemFrame m0 w16 (rt ++ priv ++ [(r4 - 4192, r4 + 72)]))
    (hw2 : MemFrame ((w16.writeLE (t + 8) 8 a).writeLE (r4 - 96) 8 b) w9 (rt ++ [(r4 - 96 - 4096, r4 - 96)]))
    (hw1 : MemFrame (((((((w9.writeLE s2 8 c).writeLE (s2 + 8) 8 d).writeLE t 8 e).writeLE (t + 24) 8 f).writeLE
        (t + 16) 8 g).writeLE (t + 32) 8 q).writeLE (r4 - 96) 8 c4) w2 (rt ++ [(r4 - 96 - 4096, r4 - 96)]))
    (hr4 : 4192 ≤ r4) (ht : InRanges t 48 rt) (hs2 : InRanges s2 16 rt) :
    MemFrame m0 w2 (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) := by
  have hW : (r4 - 4192, r4 + 72) ∈ rt ++ priv ++ [(r4 - 4192, r4 + 72)] := by simp
  have key : ∀ x n, Outside x n (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) →
      Outside x n (rt ++ [(r4 - 96 - 4096, r4 - 96)]) := by
    intro x n ho
    simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at ho ⊢
    refine ⟨ho.1.1, ?_⟩
    omega
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ := inRanges_fields ht (rs' := rt) (fun r hr => hr)
  obtain ⟨g0, g1⟩ : InRanges s2 8 rt ∧ InRanges (s2 + 8) 8 rt :=
    ⟨inRanges16_lo hs2, inRanges16_hi hs2⟩
  have A : MemFrame m0 ((w16.writeLE (t + 8) 8 a).writeLE (r4 - 96) 8 b) (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) :=
    (frame_writeLE_rt a hB f1).writeLE _ hW (by omega) (by omega)
  have B : MemFrame m0 w9 (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) :=
    A.trans hw2 (fun x n ho => ⟨ho, key x n ho⟩)
  have C : MemFrame m0 (((((((w9.writeLE s2 8 c).writeLE (s2 + 8) 8 d).writeLE t 8 e).writeLE (t + 24) 8 f).writeLE
        (t + 16) 8 g).writeLE (t + 32) 8 q).writeLE (r4 - 96) 8 c4) (rt ++ priv ++ [(r4 - 4192, r4 + 72)]) :=
    (((((((frame_writeLE_rt c B g0)).writeLE_inRanges d (InRanges.of_subset g1 (by intro r hr; simp [List.mem_append, hr]))).writeLE_inRanges
      e (InRanges.of_subset f0 (by intro r hr; simp [List.mem_append, hr]))).writeLE_inRanges
      f (InRanges.of_subset f3 (by intro r hr; simp [List.mem_append, hr]))).writeLE_inRanges
      g (InRanges.of_subset f2 (by intro r hr; simp [List.mem_append, hr]))).writeLE_inRanges
      q (InRanges.of_subset f4 (by intro r hr; simp [List.mem_append, hr]))).writeLE _ hW (by omega) (by omega)
  exact C.trans hw1 (fun x n ho => ⟨ho, key x n ho⟩)


theorem outside_of_apart3 {a n q m t k : Nat} {L : List (Nat × Nat)} (h1 : Janus.Contracts.ApartAll a n L)
    (h2 : Janus.Apart a n q m) (h3 : Janus.Apart a n t k) : Outside a n (L ++ [(q, q + m)] ++ [(t, t + k)]) := by
  have := h1.outside
  simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
  simp only [Janus.Apart] at h2 h3
  refine ⟨⟨this, ?_⟩, ?_⟩ <;> omega

/-- the invariant after a store into a write-barrier slot (inside `rt`, outside the live set) -/
theorem inv_slot1 {R : RtInv} {b g buf x : Nat} {L rt : List (Nat × Nat)} {m : Janus.Arm64.Memory}
    (hI : InvSlots R b L g rt m buf 1) (hrt : InRanges buf 8 rt) (hout : Outside buf 8 L) :
    R.inv b L g (view rt L (m.writeLE buf 8 x)) := by
  rw [view_writeLE_vis hrt hout]
  exact hI _ (((MemFrame.refl _ _).writeLE x (r := (buf, buf + 8 * 1)) (by simp) (by omega) (by omega)))

/-- the bytes copied into the fresh string `q`, read back through the write-barrier branch's stores, the two barrier
frames and the `newobject` frame -/
theorem te_copy1 {M w2 w9 w16 w10 M0 : Janus.Arm64.Memory} {L : List (Nat × Nat)}
    {t q bs sl sp k r4 s2 s6 a1 a2 a3 v1 v2 v3 y z c1 c2 c3 c4 c5 c6 c7 d1 d2 X : Nat}
    (hM : M = (w2.writeLE s6 8 y).writeLE (t + 40) 8 z)
    (hL2 : LiveFrame (((((((w9.writeLE s2 8 c1).writeLE (s2 + 8) 8 c2).writeLE t 8 c3).writeLE (t + 24) 8 c4).writeLE
      (t + 16) 8 c5).writeLE (t + 32) 8 c6).writeLE (r4 - 96) 8 c7) w2 (L ++ [(q, q + bs)] ++ [(t, t + 48)]) [])
    (hL1 : LiveFrame ((w16.writeLE (t + 8) 8 d1).writeLE (r4 - 96) 8 d2) w9 (L ++ [(q, q + bs)] ++ [(t, t + 48)]) [])
    (hL0 : LiveFrame (((w10.writeLE a1 8 v1).writeLE a2 8 v2).writeLE a3 8 v3) w16 (L ++ [(q, q + bs)]) [])
    (hk : k < sl) (hsl : sl ≤ bs)
    (hq6 : s6 + 8 ≤ q ∨ q + bs ≤ s6) (hq2 : s2 + 16 ≤ q ∨ q + bs ≤ s2) (hqt : t + 48 ≤ q ∨ q + bs ≤ t)
    (hqr : r4 - 96 + 8 ≤ q ∨ q + bs ≤ r4 - 96)
    (hd1 : q + k + 1 ≤ a1 ∨ a1 + 8 ≤ q + k) (hd2 : q + k + 1 ≤ a2 ∨ a2 + 8 ≤ q + k)
    (hd3 : q + k + 1 ≤ a3 ∨ a3 + 8 ≤ q + k)
    (hCop : Mem.Copied M0 w10 q sp sl) (hsrc : M0.readLE (sp + k) 1 = X) :
    M.readLE (q + k) 1 = X := by
  subst hM
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  rw [hL2.readLE_nil _ _ ⟨(q, q + bs), by simp, by omega, by omega⟩]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  rw [hL1.readLE_nil _ _ ⟨(q, q + bs), by simp, by omega, by omega⟩]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  rw [hL0.readLE_nil _ _ ⟨(q, q + bs), by simp, by omega, by omega⟩]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  rw [Janus.Arm64.Memory.readLE_one, hCop k hk, ← Janus.Arm64.Memory.readLE_one]
  exact hsrc


theorem te_f0 {M w2 w9 w16 : Janus.Arm64.Memory} {L : List (Nat × Nat)}
    {t q bs r4 s2 s6 y z c1 c2 c3 c4 c5 c6 c7 d1 d2 : Nat}
    (hM : M = (w2.writeLE s6 8 y).writeLE (t + 40) 8 z)
    (hL2 : LiveFrame (((((((w9.writeLE s2 8 c1).writeLE (s2 + 8) 8 c2).writeLE t 8 c3).writeLE (t + 24) 8 c4).writeLE
      (t + 16) 8 c5).writeLE (t + 32) 8 c6).writeLE (r4 - 96) 8 c7) w2 (L ++ [(q, q + bs)] ++ [(t, t + 48)]) [])
    (hL1 : LiveFrame ((w16.writeLE (t + 8) 8 d1).writeLE (r4 - 96) 8 d2) w9 (L ++ [(q, q + bs)] ++ [(t, t + 48)]) [])
    (hq6 : s6 + 8 ≤ t ∨ t + 48 ≤ s6) (hq2 : s2 + 16 ≤ t ∨ t + 48 ≤ s2) (hqr : r4 - 96 + 8 ≤ t ∨ t + 48 ≤ r4 - 96)
    (hb : c3 < 256 ^ 8) :
    M.readLE (t) 8 = c3 := by
  subst hM
  have e2 : InRanges (t) 8 (L ++ [(q, q + bs)] ++ [(t, t + 48)]) := ⟨(t, t + 48), by simp, by omega, by omega⟩
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  rw [hL2.readLE_nil _ _ e2]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt hb

theorem te_f1 {M w2 w9 w16 : Janus.Arm64.Memory} {L : List (Nat × Nat)}
    {t q bs r4 s2 s6 y z c1 c2 c3 c4 c5 c6 c7 d1 d2 : Nat}
    (hM : M = (w2.writeLE s6 8 y).writeLE (t + 40) 8 z)
    (hL2 : LiveFrame (((((((w9.writeLE s2 8 c1).writeLE (s2 + 8) 8 c2).writeLE t 8 c3).writeLE (t + 24) 8 c4).writeLE
      (t + 16) 8 c5).writeLE (t + 32) 8 c6).writeLE (r4 - 96) 8 c7) w2 (L ++ [(q, q + bs)] ++ [(t, t + 48)]) [])
    (hL1 : LiveFrame ((w16.writeLE (t + 8) 8 d1).writeLE (r4 - 96) 8 d2) w9 (L ++ [(q, q + bs)] ++ [(t, t + 48)]) [])
    (hq6 : s6 + 8 ≤ t ∨ t + 48 ≤ s6) (hq2 : s2 + 16 ≤ t ∨ t + 48 ≤ s2) (hqr : r4 - 96 + 8 ≤ t ∨ t + 48 ≤ r4 - 96)
    (hb : d1 < 256 ^ 8) :
    M.readLE (t + 8) 8 = d1 := by
  subst hM
  have e2 : InRanges (t + 8) 8 (L ++ [(q, q + bs)] ++ [(t, t + 48)]) := ⟨(t, t + 48), by simp, by omega, by omega⟩
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  rw [hL2.readLE_nil _ _ e2]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  rw [hL1.readLE_nil _ _ e2]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt hb

theorem te_f2 {M w2 w9 w16 : Janus.Arm64.Memory} {L : List (Nat × Nat)}
    {t q bs r4 s2 s6 y z c1 c2 c3 c4 c5 c6 c7 d1 d2 : Nat}
    (hM : M = (w2.writeLE s6 8 y).writeLE (t + 40) 8 z)
    (hL2 : LiveFrame (((((((w9.writeLE s2 8 c1).writeLE (s2 + 8) 8 c2).writeLE t 8 c3).writeLE (t + 24) 8 c4).writeLE
      (t + 16) 8 c5).writeLE (t + 32) 8 c6).writeLE (r4 - 96) 8 c7) w2 (L ++ [(q, q + bs)] ++ [(t, t + 48)]) [])
    (hL1 : LiveFrame ((w16.writeLE (t + 8) 8 d1).writeLE (r4 - 96) 8 d2) w9 (L ++ [(q, q + bs)] ++ [(t, t + 48)]) [])
    (hq6 : s6 + 8 ≤ t ∨ t + 48 ≤ s6) (hq2 : s2 + 16 ≤ t ∨ t + 48 ≤ s2) (hqr : r4 - 96 + 8 ≤ t ∨ t + 48 ≤ r4 - 96)
    (hb : c5 < 256 ^ 8) :
    M.readLE (t + 16) 8 = c5 := by
  subst hM
  have e2 : InRanges (t + 16) 8 (L ++ [(q, q + bs)] ++ [(t, t + 48)]) := ⟨(t, t + 48), by simp, by omega, by omega⟩
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  rw [hL2.readLE_nil _ _ e2]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt hb

theorem te_f3 {M w2 w9 w16 : Janus.Arm64.Memory} {L : List (Nat × Nat)}
    {t q bs r4 s2 s6 y z c1 c2 c3 c4 c5 c6 c7 d1 d2 : Nat}
    (hM : M = (w2.writeLE s6 8 y).writeLE (t + 40) 8 z)
    (hL2 : LiveFrame (((((((w9.writeLE s2 8 c1).writeLE (s2 + 8) 8 c2).writeLE t 8 c3).writeLE (t + 24) 8 c4).writeLE
      (t + 16) 8 c5).writeLE (t + 32) 8 c6).writeLE (r4 - 96) 8 c7) w2 (L ++ [(q, q + bs)] ++ [(t, t + 48)]) [])
    (hL1 : LiveFrame ((w16.writeLE (t + 8) 8 d1).writeLE (r4 - 96) 8 d2) w9 (L ++ [(q, q + bs)] ++ [(t, t + 48)]) [])
    (hq6 : s6 + 8 ≤ t ∨ t + 48 ≤ s6) (hq2 : s2 + 16 ≤ t ∨ t + 48 ≤ s2) (hqr : r4 - 96 + 8 ≤ t ∨ t + 48 ≤ r4 - 96)
    (hb : c4 < 256 ^ 8) :
    M.readLE (t + 24) 8 = c4 := by
  subst hM
  have e2 : InRanges (t + 24) 8 (L ++ [(q, q + bs)] ++ [(t, t + 48)]) := ⟨(t, t + 48), by simp, by omega, by omega⟩
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  rw [hL2.readLE_nil _ _ e2]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt hb

theorem te_f4 {M w2 w9 w16 : Janus.Arm64.Memory} {L : List (Nat × Nat)}
    {t q bs r4 s2 s6 y z c1 c2 c3 c4 c5 c6 c7 d1 d2 : Nat}
    (hM : M = (w2.writeLE s6 8 y).writeLE (t + 40) 8 z)
    (hL2 : LiveFrame (((((((w9.writeLE s2 8 c1).writeLE (s2 + 8) 8 c2).writeLE t 8 c3).writeLE (t + 24) 8 c4).writeLE
      (t + 16) 8 c5).writeLE (t + 32) 8 c6).writeLE (r4 - 96) 8 c7) w2 (L ++ [(q, q + bs)] ++ [(t, t + 48)]) [])
    (hL1 : LiveFrame ((w16.writeLE (t + 8) 8 d1).writeLE (r4 - 96) 8 d2) w9 (L ++ [(q, q + bs)] ++ [(t, t + 48)]) [])
    (hq6 : s6 + 8 ≤ t ∨ t + 48 ≤ s6) (hq2 : s2 + 16 ≤ t ∨ t + 48 ≤ s2) (hqr : r4 - 96 + 8 ≤ t ∨ t + 48 ≤ r4 - 96)
    (hb : c6 < 256 ^ 8) :
    M.readLE (t + 32) 8 = c6 := by
  subst hM
  have e2 : InRanges (t + 32) 8 (L ++ [(q, q + bs)] ++ [(t, t + 48)]) := ⟨(t, t + 48), by simp, by omega, by omega⟩
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  rw [hL2.readLE_nil _ _ e2]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt hb

theorem te_f5 {M w2 w9 w16 : Janus.Arm64.Memory} {L : List (Nat × Nat)}
    {t q bs r4 s2 s6 y z c1 c2 c3 c4 c5 c6 c7 d1 d2 : Nat}
    (hM : M = (w2.writeLE s6 8 y).writeLE (t + 40) 8 z)
    (hL2 : LiveFrame (((((((w9.writeLE s2 8 c1).writeLE (s2 + 8) 8 c2).writeLE t 8 c3).writeLE (t + 24) 8 c4).writeLE
      (t + 16) 8 c5).writeLE (t + 32) 8 c6).writeLE (r4 - 96) 8 c7) w2 (L ++ [(q, q + bs)] ++ [(t, t + 48)]) [])
    (hL1 : LiveFrame ((w16.writeLE (t + 8) 8 d1).writeLE (r4 - 96) 8 d2) w9 (L ++ [(q, q + bs)] ++ [(t, t + 48)]) [])
    (hq6 : s6 + 8 ≤ t ∨ t + 48 ≤ s6) (hq2 : s2 + 16 ≤ t ∨ t + 48 ≤ s2) (hqr : r4 - 96 + 8 ≤ t ∨ t + 48 ≤ r4 - 96)
    (hb : z < 256 ^ 8) :
    M.readLE (t + 40) 8 = z := by
  subst hM
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt hb


theorem win_a {r4 q m d : Nat} (h : r4 - 4192 + 4264 ≤ q ∨ q + m ≤ r4 - 4192) (hlow : 4192 ≤ r4) (h1 : 8 ≤ d)
    (h2 : d ≤ 4192) : r4 - d + 8 ≤ q ∨ q + m ≤ r4 - d := by omega

theorem win_k {q m k a : Nat} (h : a + 8 ≤ q ∨ q + m ≤ a) (hk : k < m) : q + k + 1 ≤ a ∨ a + 8 ≤ q + k := by omega

end Fv256.Amd64.SfdToError
