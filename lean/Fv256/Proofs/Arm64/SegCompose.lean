import Janus

/-!
# Composition glue for arm64 run segments

`ReachesRet p mid S Q` (Janus.Tactic) says: from `S`, `p` reaches the address `mid` in a state satisfying `Q`
(with `mid` the exit address; for the function's own return it is the return address). A segment lemma
`seg_k (S) (hpc : S.pc = ofNat pc_k) (hpre : Q_{k-1} S) : ReachesRet p (ofNat pc_{k+1}) S Q_k`
composes with `seg_trans`. arm64 twin of `Fv256.SegCompose` (amd64).
-/

open Janus Janus.Arm64 Janus.Tactic

namespace Fv256.Arm64.SegCompose

theorem seg_trans {p : Janus.Program} {ret mid : BitVec 64} {S : State} {Q Qmid : State → Prop}
    (h1 : ReachesRet p mid S Qmid)
    (h2 : ∀ S', S'.pc = mid → Qmid S' → ReachesRet p ret S' Q) :
    ReachesRet p ret S Q := by
  obtain ⟨k, s', hs, hr, hq⟩ := h1
  obtain ⟨j, s'', hs2, hr2, hq2⟩ := h2 s' hr hq
  exact ⟨k + j, s'', hs.trans hs2, hr2, hq2⟩

theorem seg_mono {p : Janus.Program} {ret : BitVec 64} {S : State} {Q Q' : State → Prop}
    (h : ReachesRet p ret S Q) (hQ : ∀ S', Q S' → Q' S') : ReachesRet p ret S Q' := by
  obtain ⟨k, s', hs, hr, hq⟩ := h
  exact ⟨k, s', hs, hr, hQ s' hq⟩

theorem seg_trans' {p : Janus.Program} {ret mid : BitVec 64} {S : State} {Q R T : State → Prop}
    (h1 : ReachesRet p mid S Q) (hQR : ∀ S', Q S' → R S')
    (h2 : ∀ S', S'.pc = mid → R S' → ReachesRet p ret S' T) : ReachesRet p ret S T :=
  seg_trans h1 (fun S' hr hq => h2 S' hr (hQR S' hq))

end Fv256.Arm64.SegCompose
