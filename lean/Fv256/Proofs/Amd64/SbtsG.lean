import Janus
import Fv256.Proofs.Arm64.SbtsG
import Fv256.Spec.Amd64.SbtsG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
open Fv256.Arm64.SbtsG

namespace Fv256.Amd64.SbtsG

/-- Readiness (amd64): goroutine `g0` (`R14`), and for every memory with this runtime view the live part of the call's precondition holds
with a budget that also covers `extra` further bytes.  The stack check is the spec's `guard`, not part of it. -/
def HG64 (R : RtInv) (addr extra g0 : Nat) : RtReady :=
  fun args g sp v => g = g0 ∧ ∀ m, rtView R.rt m = v →
    ∃ (L : List (Nat × Nat)) (b : Nat),
      LiveAt R addr args L b (slicebytetostringLive.cost args m + extra) g m (window64 sp 4096 3)

theorem contract_G64 {p : Janus.Amd64.Program} {addr : Nat} {R : RtInv} {st : Nat}
    (h : RtLiveContract64 p addr 4096 R (slicebytetostringSpec st) slicebytetostringLive) (g0 extra : Nat) :
    RtContract64 p addr R.rt 4096 (HG64 R addr extra g0) (sbtsG st (Gp R g0 extra)) := by
  intro s hpc hpre
  obtain ⟨hc, hp, hr, hg, hH⟩ := hpre
  have hH' := ready_of (by rfl) hH
  obtain ⟨hgg, hlive⟩ := hH'
  obtain ⟨L, b, hl⟩ := hlive s.mem rfl
  obtain ⟨hok, hinv, hcost, hs1, hs2⟩ := hl
  obtain ⟨⟨g1, g2, g3⟩, g4⟩ := hg
  have hcost' : slicebytetostringLive.cost (argWords64 s 3) s.mem + extra ≤ b := hcost
  have h1 := h L b s hpc ⟨hc, hp, hr, trivial, ⟨⟨g1, g2, g3⟩, g4⟩, ⟨hok, hinv, Nat.le_trans (Nat.le_add_right _ _) hcost', hs1, hs2⟩⟩
  obtain ⟨k, s', hst, hret, r0, r1, r2, junk, f, x, yh, m, zh, kr, e1, e2, e3, e4, e5, e6, e7⟩ := h1
  refine ⟨k, s', hst, hret, r0, r1, r2, junk, f, x, yh, m, zh, kr, e1, e2, ⟨e3, ?_⟩⟩
  refine ⟨L ++ liveAdds slicebytetostringLive (argWords64 s 3) s.mem r0.toNat r1.toNat r2.toNat,
    b - slicebytetostringLive.cost (argWords64 s 3) s.mem, ?_, ?_, fun hpos => inRanges_adds _ _ _ _ _ _ hpos⟩
  · rw [← hgg]; exact e7
  · omega

end Fv256.Amd64.SbtsG
