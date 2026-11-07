import Janus

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts

namespace Fv256.Arm64.SbtsG

/-- `slicebytetostring`'s spec with a ghost fact `G` about the result and the memory added to the postcondition. -/
@[reducible] def sbtsG (st : Nat) (G : Nat → Nat → Memory → Prop) : RtSpec :=
  { slicebytetostringSpec st with
    guard := some 4096
    post := fun rt a m0 r0 r1 r2 m => (slicebytetostringSpec st).post rt a m0 r0 r1 r2 m ∧ G r0 r1 m }

/-- The runtime is live after the call: invariant for a live set `L1` containing the result string, with budget at least `extra`. -/
def Gp (R : RtInv) (g0 extra : Nat) : Nat → Nat → Memory → Prop :=
  fun r0 r1 m => ∃ (L1 : List (Nat × Nat)) (b1 : Nat), R.inv b1 L1 g0 (view R.rt L1 m) ∧ extra ≤ b1 ∧
    (0 < r1 → InRanges r0 r1 L1)

/-- Readiness: goroutine `g0`, and for every memory with this runtime view the live part of the call's precondition holds (the request is
served, the invariant holds for some live set and budget, the window is apart from the live set and the runtime ranges) with a budget
that also covers `extra` further bytes.  The stack check is NOT part of it (it depends on memory outside the runtime view); the spec
carries it as its `guard`. -/
def HG (R : RtInv) (addr extra g0 : Nat) : RtReady :=
  fun args g sp v => g = g0 ∧ ∀ m, rtView R.rt m = v →
    ∃ (L : List (Nat × Nat)) (b : Nat),
      LiveAt R addr args L b (slicebytetostringLive.cost args m + extra) g m (windowAt sp 4096 3)

theorem view_congr {rt L : List (Nat × Nat)} {m m' : Memory} (h : rtView rt m = rtView rt m') : view rt L m = view rt L m' := by
  have hb := congrArg Janus.Arm64.Memory.bytes h
  have hr := congrArg Janus.Arm64.Memory.regions h
  simp only [rtView] at hb hr
  simp only [view]
  congr 1
  funext a
  have := congrFun hb a
  by_cases hin : rt.any (fun r => decide (r.1 ≤ a) && decide (a < r.2)) = true
  · rw [if_pos hin, if_pos hin] at this
    have h2 : inRs rt a = true := hin
    simp only [h2]
    rw [this]
  · have h2 : inRs rt a = false := by simpa [inRs] using hin
    simp only [h2]
    simp

theorem Gp_congr (R : RtInv) (g0 extra : Nat) (r0 r1 : Nat) {m m' : Memory} (h : rtView R.rt m = rtView R.rt m') :
    Gp R g0 extra r0 r1 m → Gp R g0 extra r0 r1 m' := by
  rintro ⟨L1, b1, hi, hb, hr⟩
  exact ⟨L1, b1, by rw [← view_congr h]; exact hi, hb, hr⟩

theorem inRanges_adds (a : List Nat) (m : Memory) (r0 r1 r2 : Nat) (L : List (Nat × Nat)) (h : 0 < r1) :
    InRanges r0 r1 (L ++ liveAdds slicebytetostringLive a m r0 r1 r2) := by
  simp only [liveAdds, slicebytetostringLive, range0, if_neg (show ¬ r1 = 0 by omega)]
  split <;> exact ⟨(r0, r0 + r1), by simp, Nat.le_refl _, Nat.le_refl _⟩

theorem contract_G {p : Program} {addr : Nat} {R : RtInv} {st : Nat}
    (h : RtLiveContract p addr 4096 R (slicebytetostringSpec st) slicebytetostringLive) (g0 extra : Nat) :
    RtContract p addr R.rt 4096 (HG R addr extra g0) (sbtsG st (Gp R g0 extra)) := by
  intro s hpc hpre
  obtain ⟨hc, hp, hr, hg, hH⟩ := hpre
  have hH' := ready_of (by rfl) hH
  obtain ⟨hgg, hlive⟩ := hH'
  obtain ⟨L, b, hl⟩ := hlive s.mem rfl
  obtain ⟨hok, hinv, hcost, hs1, hs2⟩ := hl
  obtain ⟨⟨g1, g2, g3⟩, g4⟩ := hg
  have hcost' : slicebytetostringLive.cost (argWords s 3) s.mem + extra ≤ b := hcost
  have h1 := h L b s hpc ⟨hc, hp, hr, trivial, ⟨⟨g1, g2, g3⟩, g4⟩, ⟨hok, hinv, Nat.le_trans (Nat.le_add_right _ _) hcost', hs1, hs2⟩⟩
  obtain ⟨k, s', hst, hret, r0, r1, r2, junk, f, v, m, ex, ep, e1, e2, e3, e4, e5, e6, e7⟩ := h1
  refine ⟨k, s', hst, hret, r0, r1, r2, junk, f, v, m, ex, ep, e1, e2, ⟨e3, ?_⟩⟩
  refine ⟨L ++ liveAdds slicebytetostringLive (argWords s 3) s.mem r0.toNat r1.toNat r2.toNat,
    b - slicebytetostringLive.cost (argWords s 3) s.mem, ?_, ?_, fun hpos => inRanges_adds _ _ _ _ _ _ hpos⟩
  · rw [← hgg]; exact e7
  · omega

end Fv256.Arm64.SbtsG

