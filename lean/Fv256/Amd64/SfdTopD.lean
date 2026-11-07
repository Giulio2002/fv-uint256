import Fv256.Amd64.SfdTopC

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd
  Fv256.Amd64.SfdTopSpec Fv256.Amd64.SfdTopCfg Fv256.Amd64.SfdTopBr

namespace Fv256.Amd64.SfdTop

/-- the zero-skip loop, by induction on the bytes left -/
theorem top_loop (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s) :
    ∀ (k j : Nat) (S : State), nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat - j = k →
      S.rip = BitVec.ofNat 64 (sfd + 0xe0) → LoopInv R R2 T b L lo hi z pS nS s j S →
      ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (sfd + 0x12a)) S
        (fun S' => ∃ i, TailInv R R2 T b L lo hi z pS nS s i S') := by
  intro k
  induction k with
  | zero =>
    intro j S hk hpc hI
    exact Fv256.SegCompose.seg_mono (top_lend impl R R2 T b L lo hi z pS nS s hpre S j hpc hI (by omega)) (fun S' h => ⟨_, h⟩)
  | succ k ih =>
    intro j S hk hpc hI
    have hjm : j + 1 ≤ nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by omega
    by_cases h48 : Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) = 48
    · exact top_ls impl R R2 T b L lo hi z pS nS s hpre S j hpc hI hjm h48
        (fun S' hpc' hI' => ih (j + 1) S' (by omega) hpc' hI')
    · by_cases h127 : Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) ≤ 127
      · exact Fv256.SegCompose.seg_mono (top_lb impl R R2 T b L lo hi z pS nS s hpre S j hpc hI hjm h127 h48) (fun S' h => ⟨_, h⟩)
      · exact Fv256.SegCompose.seg_mono (top_ld impl R R2 T b L lo hi z pS nS s hpre S j hpc hI hjm (by omega)) (fun S' h => ⟨_, h⟩)

/-- from the entry to the length compare: the stripped number is `[startPos, n)` -/
theorem top_front (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 sfd)
    (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (sfd + 0x57)) s (TopMid R R2 T b L lo hi z pS nS s) := by
  refine Fv256.SegCompose.seg_trans (top_pro impl R R2 T b L lo hi z pS nS s hpc hpre) ?_
  intro S hpc1 hA
  by_cases hR1 : S.regs 1 = 0#64
  · exact top_b0 impl R R2 T b L lo hi z pS nS s S hpc1 hA hR1
  · by_cases hbz : Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) = 48
    · refine Fv256.SegCompose.seg_trans (top_b2 impl R R2 T b L lo hi z pS nS s hpre S hpc1 hA hR1 hbz) ?_
      intro S2 hpc2 hL
      refine Fv256.SegCompose.seg_trans (top_loop impl R R2 T b L lo hi z pS nS s hpre _ 0 S2 rfl hpc2 hL) ?_
      intro S3 hpc3 hT
      obtain ⟨i, hTi⟩ := hT
      exact top_tail impl R R2 T b L lo hi z pS nS s hpre S3 i hpc3 hTi
    · exact top_b1 impl R R2 T b L lo hi z pS nS s hpre S hpc1 hA hR1 hbz

end Fv256.Amd64.SfdTop
