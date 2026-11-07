import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SpecScan
import Fv256.IndexByteSpec
import Fv256.IbsA64
import Fv256.Arm64.SfdTopSpec
import Fv256.Arm64.SfdEnvC
import Fv256.Arm64.ScanSciSpec
import Fv256.Arm64.ScanSciBase

/-!
# `scanScientificFromString` (arm64): after the exponent parse: range check, `Exp`, `MulOverflow`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSciSpec

namespace Fv256.Arm64.ScanSci

theorem found5 (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64) (hsfd : HSfd impl R R2 T) (hexp : HExp impl) (hmo : HMo impl)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s) (hn : nS.toNat ≠ 0)
    (v e : Nat)
    (hsci : Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat =
      (if 77 < e ∨ 2 ^ 256 ≤ v * 10 ^ e then Fv256.I.Res.range else Fv256.I.Res.ok (v * 10 ^ e)))
    (S5 : State) (hFr : Fr lo dst pS nS s S5) (hval : Janus.Spec.val256 S5.mem dst.toNat = v)
    (hexpv : Janus.Spec.val256 S5.mem (S5.sp.toNat + 72) = e) (hx0z : S5.regs 0 = 0)
    (hpc5 : S5.pc = BitVec.ofNat 64 (sciEntry + 0xd4)) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S5 (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  sorry

end Fv256.Arm64.ScanSci
