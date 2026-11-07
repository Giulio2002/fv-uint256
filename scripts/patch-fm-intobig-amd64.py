#!/usr/bin/env python3
"""Patch of the generated FM/IntoBig* modules (run by gen-fm-intobig-amd64.sh): IntoBig's postcondition `Post` gets a fifth conjunct
(for z != 0 and *bp = 0 on entry, the fresh big.Int block and its word array lie in R.rt), which Format's big path needs to keep the
BigObj across the push of the return address of the second call. Every replacement must occur exactly once."""
import sys
D = sys.argv[1]
def patch(fn, reps):
    p = f"{D}/{fn}.lean"
    s = open(p).read()
    for old, new in reps:
        assert s.count(old) == 1, (fn, s.count(old), old[:80])
        s = s.replace(old, new)
    open(p, "w").write(s)

patch("IntoBigDefs", [
("""  (s.mem.readLE bp.toNat 8 = 0 →
    MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
      (bp.toNat, bp.toNat + 8)]))
""", """  (s.mem.readLE bp.toNat 8 = 0 →
    MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
      (bp.toNat, bp.toNat + 8)])) ∧
  (z.toNat ≠ 0 → s.mem.readLE bp.toNat 8 = 0 →
    InRanges (s'.mem.readLE bp.toNat 8) 32 R.rt ∧ InRanges (s'.mem.readLE (s'.mem.readLE bp.toNat 8 + 8) 8) 32 R.rt)
"""),
("""theorem post_of_tail (R : RtInv) (z bp : BitVec 64) (s : State) (P : Nat) (hz0 : z.toNat ≠ 0)
""", """theorem post_of_tail (R : RtInv) (z bp : BitVec 64) (s : State) (P A : Nat) (hz0 : z.toNat ≠ 0)
    (hPin : s.mem.readLE bp.toNat 8 = 0 → InRanges P 32 R.rt)
"""),
("""      IsReturn (fun s' => ABIReturn s s' ∧ BigOut s'.mem bp.toNat P (val256 s.mem z.toNat) ∧
        MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
          (bp.toNat, bp.toNat + 8), (P, P + 32)])) o →""",
"""      IsReturn (fun s' => ABIReturn s s' ∧ BigOut s'.mem bp.toNat P (val256 s.mem z.toNat) ∧
        MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
          (bp.toNat, bp.toNat + 8), (P, P + 32)]) ∧ (s'.mem.readLE (P + 8) 8 = A ∧ InRanges A 32 R.rt)) o →"""),
("""  | returned s' => exact ⟨ho.1, fun h => absurd h hz0, fun _ => ⟨P, ho.2.1⟩, ho.2.2.mono hw, fun h0 => ho.2.2.mono (hn h0)⟩""",
"""  | returned s' =>
    refine ⟨ho.1, fun h => absurd h hz0, fun _ => ⟨P, ho.2.1⟩, ho.2.2.1.mono hw, fun h0 => ho.2.2.1.mono (hn h0), fun _ h0 => ?_⟩
    obtain ⟨ap, len, cap, hbp, -⟩ := ho.2.1
    rw [hbp, ho.2.2.2.1]
    exact ⟨hPin h0, ho.2.2.2.2⟩"""),
])

patch("IntoBigFinF", [
("""    | refine ⟨fun h => absurd h hz0, fun _ => ⟨P, ?_⟩, ?_, fun h0 => absurd (hPs.symm.trans h0) hP0⟩
    | refine ⟨hx15, fun h => absurd h hz0, fun _ => ⟨P, ?_⟩, ?_, fun h0 => absurd (hPs.symm.trans h0) hP0⟩""",
"""    | refine ⟨fun h => absurd h hz0, fun _ => ⟨P, ?_⟩, ?_, fun h0 => absurd (hPs.symm.trans h0) hP0, fun _ h0 => absurd (hPs.symm.trans h0) hP0⟩
    | refine ⟨hx15, fun h => absurd h hz0, fun _ => ⟨P, ?_⟩, ?_, fun h0 => absurd (hPs.symm.trans h0) hP0, fun _ h0 => absurd (hPs.symm.trans h0) hP0⟩"""),
])

patch("IntoBigTail", [
("""    (L0 : List (Nat × Nat)) (hPrt : (L0 = [] ∧ Outside P 32 R.rt) ∨ (L0 = [(P, P + 32)] ∧ InRanges P 32 R.rt))
""", """    (L0 : List (Nat × Nat)) (hPrt : (L0 = [] ∧ Outside P 32 R.rt) ∨ (L0 = [(P, P + 32)] ∧ InRanges P 32 R.rt))
    (hAin : InRanges A' 32 R.rt)
"""),
("""        MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24), (bp.toNat, bp.toNat + 8), (P, P + 32)])) := by
  have h0 :""", """        MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24), (bp.toNat, bp.toNat + 8), (P, P + 32)]) ∧
        (s'.mem.readLE (P + 8) 8 = A' ∧ InRanges A' 32 R.rt)) := by
  have h0 :"""),
("""          tail0_frame hfr2⟩)
    · first
      | (set_option maxHeartbeats 600000 in exact ⟨tail1_bigout (sp := (s.regs 4).toNat) hfr2 h_rdP hPa hP48 hAacc hA48 hbP hAP hlen hword hnorm hzero hbpo hbpd hb'
            (unpush1 (show MemFrame _ _ _ by janus_assumption) (by omega)) (live_unpush (show LiveFrame _ _ _ _ by janus_assumption) (by intro r hr; simp at hr; subst hr; simp; omega)) ⟨(A', A' + 32), by simp, Nat.le_refl _, Nat.le_refl _⟩ (show InRanges (BitVec.toNat _) 16 R.rt by janus_assumption)""",
"""          tail0_frame hfr2, hAin⟩)
    · first
      | (set_option maxHeartbeats 600000 in exact ⟨tail1_bigout (sp := (s.regs 4).toNat) hfr2 h_rdP hPa hP48 hAacc hA48 hbP hAP hlen hword hnorm hzero hbpo hbpd hb'
            (unpush1 (show MemFrame _ _ _ by janus_assumption) (by omega)) (live_unpush (show LiveFrame _ _ _ _ by janus_assumption) (by intro r hr; simp at hr; subst hr; simp; omega)) ⟨(A', A' + 32), by simp, Nat.le_refl _, Nat.le_refl _⟩ (show InRanges (BitVec.toNat _) 16 R.rt by janus_assumption)"""),
("""          tail1_frame hfr2 hb' (unpush1 (show MemFrame _ _ _ by janus_assumption) (by omega)) (show InRanges (BitVec.toNat _) 16 R.rt by janus_assumption)⟩)
  · subst hL""", """          tail1_frame hfr2 hb' (unpush1 (show MemFrame _ _ _ by janus_assumption) (by omega)) (show InRanges (BitVec.toNat _) 16 R.rt by janus_assumption),
          hAin⟩)
  · subst hL"""),
("""          tail0_frame hfr2⟩)
    · first
      | (obtain ⟨hAw""", """          tail0_frame hfr2, hAin⟩)
    · first
      | (obtain ⟨hAw"""),
("""              hfr2 hb' (unpush1 (show MemFrame _ _ _ by janus_assumption) (by omega)) (show InRanges (BitVec.toNat _) 16 R.rt by janus_assumption)⟩)

end""", """              hfr2 hb' (unpush1 (show MemFrame _ _ _ by janus_assumption) (by omega)) (show InRanges (BitVec.toNat _) 16 R.rt by janus_assumption),
            hAin⟩)

end"""),
("""set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- The allocating path after the copy""", """theorem rdP8 (X : Memory) (P A' : Nat) (h : A' < 2 ^ 64) : ((X.writeLE (P + 8) 8 A').writeLE P 1 0).readLE (P + 8) 8 = A' := by
  rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
    show (256 : Nat) ^ 8 = 2 ^ 64 by decide, Nat.mod_eq_of_lt h]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- The allocating path after the copy"""),
])

# Slow3: slowTail gets hAin (the array block is in R.rt: hInR), post_of_tail gets A and hPin
patch("IntoBigSlow3", [
("""      hn (fun i h1 h2 => hz i h1 h2) [] (Or.inl ⟨rfl, hX⟩)
      (by rw [hm]; rw [view_words4_live _ _ _ _ _ _ _ _ ⟨(BitVec.toNat w7, BitVec.toNat w7 + 32), by simp, Nat.le_refl _, Nat.le_refl _⟩]; exact hInv))
      (fun o ho => post_of_tail R z bp s P hz0 ?hn o ho ?hw)
    case hn => exact fun h0 => absurd (hPs1.symm.trans h0) hP0""",
"""      hn (fun i h1 h2 => hz i h1 h2) [] (Or.inl ⟨rfl, hX⟩) hInR
      (by rw [hm]; rw [view_words4_live _ _ _ _ _ _ _ _ ⟨(BitVec.toNat w7, BitVec.toNat w7 + 32), by simp, Nat.le_refl _, Nat.le_refl _⟩]; exact hInv))
      (fun o ho => post_of_tail R z bp s P (BitVec.toNat w7) hz0 ?hPin ?hn o ho ?hw)
    case hPin => exact fun h0 => absurd (hPs1.symm.trans h0) hP0
    case hn => exact fun h0 => absurd (hPs1.symm.trans h0) hP0"""),
("""      hn (fun i h1 h2 => hz i h1 h2) [(P, P + 32)] (Or.inr ⟨rfl, hX⟩)
      (by rw [hm]; rw [view_words4_live _ _ _ _ _ _ _ _ ⟨(BitVec.toNat w7, BitVec.toNat w7 + 32), by simp, Nat.le_refl _, Nat.le_refl _⟩]; exact hInv))
      (fun o ho => post_of_tail R z bp s P hz0 ?hn o ho ?hw)
    case hn =>""",
"""      hn (fun i h1 h2 => hz i h1 h2) [(P, P + 32)] (Or.inr ⟨rfl, hX⟩) hInR
      (by rw [hm]; rw [view_words4_live _ _ _ _ _ _ _ _ ⟨(BitVec.toNat w7, BitVec.toNat w7 + 32), by simp, Nat.le_refl _, Nat.le_refl _⟩]; exact hInv))
      (fun o ho => post_of_tail R z bp s P (BitVec.toNat w7) hz0 ?hPin ?hn o ho ?hw)
    case hPin => exact fun _ => hX
    case hn =>"""),
])

patch("IntoBigT", [
("""  · refine ⟨fun _ => ?_, fun h => absurd (show z.toNat = 0 by janus_assumption) h, ?_, fun _ => ?_⟩
    all_goals (try janus64_simp)
    all_goals first
      | (with_reducible assumption)
      | janus_live
      | janus_frame
      | (trace_state; fail "x4")
  · refine ⟨fun _ => ?_, fun h => absurd (show z.toNat = 0 by janus_assumption) h, ?_, fun _ => ?_⟩""",
"""  · refine ⟨fun _ => ?_, fun h => absurd (show z.toNat = 0 by janus_assumption) h, ?_, fun _ => ?_, fun h => absurd (show z.toNat = 0 by janus_assumption) h⟩
    all_goals (try janus64_simp)
    all_goals first
      | (with_reducible assumption)
      | janus_live
      | janus_frame
      | (trace_state; fail "x4")
  · refine ⟨fun _ => ?_, fun h => absurd (show z.toNat = 0 by janus_assumption) h, ?_, fun _ => ?_, fun h => absurd (show z.toNat = 0 by janus_assumption) h⟩"""),
])
