import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecI
import Fv256.Proofs.Common.UtilI
import Fv256.Proofs.Arm64.SfdTopSpec
import Fv256.Proofs.Arm64.SfdEnvC
import Fv256.Proofs.Arm64.UnmarshalSpec
import Fv256.Proofs.Common.DecCongr
import Fv256.Proofs.Arm64.UnmarshalDec
import Fv256.Proofs.Arm64.UnmarshalHex
import Fv256.Proofs.Arm64.UnmarshalPost
import Fv256.Proofs.Arm64.FromHexLib
import Fv256.Proofs.Arm64.UnmarshalTextBra
import Fv256.Proofs.Arm64.UnmarshalTextBrb
import Fv256.Proofs.Arm64.UnmarshalTextBrc
import Fv256.Proofs.Arm64.UnmarshalTextBrx
import Fv256.Proofs.Arm64.UnmarshalTextBrX

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.UnmarshalSpec Fv256.Arm64.UnmarshalDec Fv256.Arm64.UnmarshalHex Fv256.Arm64.FromHexLib Fv256.Arm64.UnmarshalPost

namespace Fv256.Arm64.UnmarshalText

/-- the dispatch over the five paths -/
theorem correctness (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pI nI cI : BitVec 64)
    (hsb : RtLiveContract (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive)
    (hhex : ∀ (z hp len : BitVec 64), Summary (Extracted.program.link impl) fhEntry (FromHexPre z hp len) (FromHexPost z hp len))
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS') :
    Ensures (Extracted.program.link impl) Extracted.entry [z, pI, nI, cI]
      (fun s => (PreU cfg sbAddr stAddr R R2 T b L lo hi z pI nI s ∧ HexEnv R lo hi z s))
      (fun s s' => UTPost cfg R R2 lo hi z pI.toNat nI.toNat s s') := by
  intro ret hret s hs hpre
  by_cases h1 : (nI.toNat : Int) < 2
  · exact br_a impl R R2 T b L lo hi z pI nI cI hsb hhex hsfd ret hret s hs ⟨hpre, h1⟩
  by_cases h2 : Bw s.mem pI.toNat = 48
  · by_cases h3 : Bw s.mem (pI.toNat + 1) = 120
    · exact br_x impl R R2 T b L lo hi z pI nI cI hsb hhex hsfd ret hret s hs ⟨hpre, h1, h2, h3⟩
    · by_cases h4 : Bw s.mem (pI.toNat + 1) = 88
      · exact br_X impl R R2 T b L lo hi z pI nI cI hsb hhex hsfd ret hret s hs ⟨hpre, h1, h2, h3, h4⟩
      · exact br_c impl R R2 T b L lo hi z pI nI cI hsb hhex hsfd ret hret s hs ⟨hpre, h1, h2, h3, h4⟩
  · exact br_b impl R R2 T b L lo hi z pI nI cI hsb hhex hsfd ret hret s hs ⟨hpre, h1, h2⟩

end Fv256.Arm64.UnmarshalText
