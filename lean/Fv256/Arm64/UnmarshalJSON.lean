import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.Arm64.SfdTopSpec
import Fv256.Arm64.SfdEnvC
import Fv256.Arm64.UnmarshalSpec
import Fv256.Arm64.UnmarshalSpecJ
import Fv256.DecCongr
import Fv256.Arm64.UnmarshalDecJ
import Fv256.Arm64.UnmarshalDecN
import Fv256.Arm64.UnmarshalHex
import Fv256.Arm64.UnmarshalHexN
import Fv256.Arm64.UnmarshalPost
import Fv256.Arm64.UnmarshalJPost
import Fv256.Arm64.FromHexLib
import Fv256.Arm64.UnmarshalJSONJua
import Fv256.Arm64.UnmarshalJSONJud
import Fv256.Arm64.UnmarshalJSONJuc
import Fv256.Arm64.UnmarshalJSONJqa
import Fv256.Arm64.UnmarshalJSONJqb
import Fv256.Arm64.UnmarshalJSONJqc
import Fv256.Arm64.UnmarshalJSONJqx
import Fv256.Arm64.UnmarshalJSONJqX

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.UnmarshalSpec Fv256.Arm64.UnmarshalSpecJ Fv256.Arm64.UnmarshalHex Fv256.Arm64.FromHexLib Fv256.Arm64.UnmarshalPost Fv256.Arm64.UnmarshalJPost

namespace Fv256.Arm64.UnmarshalJSON

/-- the dispatch over the eight paths -/
theorem correctness (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pI nI cI : BitVec 64)
    (hsb : RtLiveContract (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive)
    (hhex : ∀ (z hp len : BitVec 64), Summary (Extracted.program.link impl) fhEntry (FromHexPre z hp len) (FromHexPost z hp len))
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS') :
    Ensures (Extracted.program.link impl) Extracted.entry [z, pI, nI, cI]
      (fun s => (PreJ cfg sbAddr stAddr R R2 T b L lo hi z pI nI s ∧ HexEnv R lo hi z s))
      (fun s s' => JPost cfg R R2 lo hi z pI.toNat nI.toNat s s') := by
  intro ret hret s hs hpre
  by_cases h1 : (nI.toNat : Int) < 2
  · exact ju_a impl R R2 T b L lo hi z pI nI cI hsb hsfd ret hret s hs ⟨hpre, h1⟩
  by_cases h2 : Bw s.mem pI.toNat = 34
  · by_cases h3 : Bw s.mem (pI.toNat + (nI.toNat - 1)) = 34
    · by_cases h4 : ((nI.toNat - 2 : Nat) : Int) < 2
      · exact jq_a impl R R2 T b L lo hi z pI nI cI hsb hsfd ret hret s hs ⟨hpre, h1, h2, h3, h4⟩
      · by_cases h5 : Bw s.mem (pI.toNat + 1) = 48
        · by_cases h6 : Bw s.mem (pI.toNat + 2) = 120
          · exact jq_x impl R R2 T b L lo hi z pI nI cI hsb hhex hsfd ret hret s hs ⟨hpre, h1, h2, h3, h4, h5, h6⟩
          · by_cases h7 : Bw s.mem (pI.toNat + 2) = 88
            · exact jq_X impl R R2 T b L lo hi z pI nI cI hsb hhex hsfd ret hret s hs ⟨hpre, h1, h2, h3, h4, h5, h6, h7⟩
            · exact jq_c impl R R2 T b L lo hi z pI nI cI hsb hsfd ret hret s hs ⟨hpre, h1, h2, h3, h4, h5, h6, h7⟩
        · exact jq_b impl R R2 T b L lo hi z pI nI cI hsb hsfd ret hret s hs ⟨hpre, h1, h2, h3, h4, h5⟩
    · exact ju_c impl R R2 T b L lo hi z pI nI cI hsb hsfd ret hret s hs ⟨hpre, h1, h2, h3⟩
  · exact ju_d impl R R2 T b L lo hi z pI nI cI hsb hsfd ret hret s hs ⟨hpre, h1, h2⟩

end Fv256.Arm64.UnmarshalJSON
