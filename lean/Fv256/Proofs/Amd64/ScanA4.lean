import Extracted
import Fv256.Proofs.Amd64.ScanSpec
import Fv256.Proofs.Amd64.ScanCfg
import Fv256.Proofs.Amd64.ScanIbsCall
import Fv256.Proofs.Amd64.ScanSfd
import Fv256.Proofs.Amd64.ScanIdx
import Fv256.Proofs.Amd64.ScanA5
open Fv256.Amd64.ScanSfd
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanCfg

namespace Fv256.Amd64.ScanA

set_option maxRecDepth 100000 in
theorem sci_after1 (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (i v : Nat) (s S4 : State) (hpc : S4.rip = BitVec.ofNat 64 (sci + 0xae))
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS')
    (hexp : ExpSumm (Extracted.program.link impl)) (hmo : ∀ z x y, MoSumm (Extracted.program.link impl) z x y)
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat ≠ 0)
    (hI : Inv4 cfg Extracted.program R R2 T b L lo hi dst p n i v s S4) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S4 (SciPost cfg R R2 b L lo hi dst p n s) := by
  have hT : TopPre0 cfg R R2 T b L lo hi dst p n s := hpre.2.1
  have hpw : p.toNat + n.toNat ≤ 2 ^ 48 := hT.pw
  have hI0 := hI
  obtain ⟨q4, q5, q14, qx, qdf, qfs, qMF, qEnv, qi, qdst, qp, qn, qret, qrbp, qsome, qlt, qdec, qval, qdl⟩ := hI
  have hnn1 : n.toNat - i = 2 → ¬ bytesAt s.mem p.toNat (i + 1) = 48 → ¬ (n.toNat - (i + 1) = 1 ∧ bytesAt s.mem p.toNat (i + 1) = 48) :=
    fun _ h2 h => h2 h.2
  by_cases c : n.toNat - i = 2 ∧ bytesAt s.mem p.toNat (i + 1) = 48
  · have hbyte : S4.mem.readLE (p.toNat + (i + 1)) 1 = bytesAt s.mem p.toNat (i + 1) := by
      unfold bytesAt
      refine qMF.readLE _ _ ?_
      simp only [outside_cons, outside_nil, and_true]
      have h1 := hT.pwin; have h2 := hT.pz
      rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> first | omega | (constructor <;> omega)
    have hbacc : S4.mem.accessible (p.toNat + (i + 1)) 1 false = true := by
      rw [qMF.accessible]
      rcases hT.pacc with h | h
      · omega
      · exact Janus.Arm64.Memory.accessible_sub s.mem h (Or.inl rfl) (by omega) (by omega)
    exact sci_nil impl R R2 T b L lo hi dst p n i v s S4 hpc hpre hn hI0 c.1 (by rw [hbyte]; exact c.2) hbacc c.2
  · by_cases h2 : n.toNat - i = 2
    · have h48 : ¬ bytesAt s.mem p.toNat (i + 1) = 48 := fun h => c ⟨h2, h⟩
      exact sci_pre2_b impl R R2 T b L lo hi dst p n i v s S4 hpc hsfd hexp hmo hpre hn hI0 (fun h => h48 h.2) h2 h48
    · have hnn : ¬ (n.toNat - (i + 1) = 1 ∧ bytesAt s.mem p.toNat (i + 1) = 48) := fun h => h2 (by omega)
      by_cases hlt : i + 1 < n.toNat
      · exact sci_pre2_pos impl R R2 T b L lo hi dst p n i v s S4 hpc hsfd hexp hmo hpre hn hI0 hnn h2 hlt
      · exact sci_pre2_end impl R R2 T b L lo hi dst p n i v s S4 hpc hsfd hexp hmo hpre hn hI0 hnn (by omega)


end Fv256.Amd64.ScanA
