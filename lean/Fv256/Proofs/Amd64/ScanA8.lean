import Extracted
import Fv256.Proofs.Amd64.ScanSpec
import Fv256.Proofs.Amd64.ScanCfg
import Fv256.Proofs.Amd64.ScanIbsCall
import Fv256.Proofs.Amd64.ScanSfd
import Fv256.Proofs.Amd64.ScanIdx
import Fv256.Proofs.Amd64.ScanA0
import Fv256.Proofs.Amd64.ScanA1
import Fv256.Proofs.Amd64.ScanA2
import Fv256.Proofs.Amd64.ScanA3
open Fv256.Amd64.ScanSfd
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanCfg

namespace Fv256.Amd64.ScanA

theorem reachesRet_bind {p : Janus.Amd64.Program} {ret1 ret2 : BitVec 64} {s : State} {Q1 Q2 : State → Prop}
    (h1 : ReachesRet p ret1 s Q1) (h2 : ∀ S, S.rip = ret1 → Q1 S → ReachesRet p ret2 S Q2) : ReachesRet p ret2 s Q2 := by
  obtain ⟨k, S, hst, hr, hq⟩ := h1
  obtain ⟨k2, S', hst2, hr2, hq2⟩ := h2 S hr hq
  exact ⟨k + k2, S', hst.trans hst2, hr2, hq2⟩

set_option maxRecDepth 100000 in
/-- Level A: the summary of `scanScientificFromString` at its entry -/
theorem sci_summary (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 sci)
    (hibs : Fv256.IndexByte.IbsLibA (Extracted.program.link impl) ibsEntry avxAddr)
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS')
    (hexp : ExpSumm (Extracted.program.link impl)) (hmo : ∀ z x y, MoSumm (Extracted.program.link impl) z x y)
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hdl : Extracted.program.DataLoaded s.mem) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) s (SciPost cfg R R2 b L lo hi dst p n s) := by
  by_cases hn : n.toNat = 0
  · exact sci_len0 impl R R2 T b L lo hi dst p n s hpc hpre hn
  · refine reachesRet_bind (sci_ibs impl R R2 T b L lo hi dst p n s hpc hibs hpre hn) (fun S hr hK => ?_)
    by_cases hidx : Fv256.IndexByte.indexOfNat (Fv256.IndexByte.bytesOf s.mem p.toNat) n.toNat 101 = 2 ^ 64 - 1
    · exact sci_none impl R R2 T b L lo hi dst p n s S hr hsfd hpre hn hK hidx
    · exact sci_some impl R R2 T b L lo hi dst p n s S hr hsfd hexp hmo hpre hn hdl hK hidx

end Fv256.Amd64.ScanA
