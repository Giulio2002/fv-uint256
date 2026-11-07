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
import Fv256.Arm64.UnmarshalJSONHead

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.UnmarshalSpec Fv256.Arm64.UnmarshalSpecJ Fv256.Arm64.UnmarshalHex Fv256.Arm64.FromHexLib Fv256.Arm64.UnmarshalPost Fv256.Arm64.UnmarshalJPost

namespace Fv256.Arm64.UnmarshalJSON

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem probe (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pI nI cI : BitVec 64)
    (hsb : RtLiveContract (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, pI, nI, cI]
      (fun s => (PreJ cfg sbAddr stAddr R R2 T b L lo hi z pI nI s ∧ HexEnv R lo hi z s) ∧ ¬ (nI.toNat : Int) < 2 ∧ (BitVec.setWidth 32 (BitVec.ofNat 64 (s.mem.readLE pI.toNat 1))).toNat = 34 ∧ (BitVec.setWidth 32 (BitVec.ofNat 64 (s.mem.readLE (pI.toNat + (nI.toNat - 1)) 1))).toNat = 34)
      (fun s s' => True) := by
  intro ret hret s hs hpre
  janus_intro hs
  obtain ⟨⟨hpreJ, henv⟩, hc1, hc2, hc3⟩ := hpre
  obtain ⟨⟨-, -, -, -, hEnv, hlo4, hhi4, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hib1, hib2⟩, hiw, -⟩, -, hext⟩ := hpreJ
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv
  have hQ : Quoted s.mem pI.toNat nI.toNat := q_of hc1 hc2 hc3
  obtain ⟨hlo5, hokH, hokD, hcost, hchunk⟩ := hext hQ
  have hbD : s.sp.toNat - 40 = 0 ∨ (s.sp.toNat - 40 ≤ 281474976710624 ∧ s.mem.accessible (s.sp.toNat - 40) 32 true = true) :=
    Or.inr ⟨by omega, Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)⟩
  janus_run until [utEntry + 0x28, utEntry + 0x6c, utEntry + 0x48]
  all_goals (trace_state)
  all_goals sorry

end Fv256.Arm64.UnmarshalJSON
