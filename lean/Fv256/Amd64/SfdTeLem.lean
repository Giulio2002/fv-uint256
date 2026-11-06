import Fv256.SumC64

/-!
# Memory-chain lemmas for the `strconv.toError` summary (amd64)

Light, extraction-free lemmas about the memory terms the `ErrSyntax` branch of `strconv.toError` produces, so that
the long `te_sum` proof does not have to walk the store chains with `simp` (it exhausts memory on the big contexts).
-/

open Janus Janus.Contracts

namespace Fv256.Amd64.SfdToError

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

end Fv256.Amd64.SfdToError
