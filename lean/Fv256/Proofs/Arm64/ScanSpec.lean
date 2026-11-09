import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecI
import Fv256.Proofs.Common.UtilI
import Fv256.Proofs.Common.SpecScan
import Fv256.Proofs.Common.IndexByteSpec
import Fv256.Proofs.Arm64.SfdTopSpec
import Fv256.Proofs.Arm64.SfdEnvC
import Fv256.Proofs.Arm64.ScanSciSpec
import Fv256.Spec.Arm64.ScanSpec

/-!
# `(*Int).Scan(src any) error` (arm64): the statement (Extracted-free)

`dst` in `X0`, the dynamic type word of `src` in `X1`, the data word in `X2`.  Plain defs only (the audit rejects consumer
structures).  The dynamic cases are decided by the type word: `0` (nil), `tyS` (`string`), `tyB` (`[]uint8`), anything else
(`unsupported type`).  Mirrors `Fv256.Amd64.ScanSpec`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSciSpec Fv256.ScanSpec

namespace Fv256.Arm64.ScanSpec

variable (C : SfdCfg)

theorem TopPre0.toTop {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {z pS nS : BitVec 64}
    {s : State} (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48)
    (h : TopPre0 C R R2 T b L lo hi z pS nS s) : TopPre C R R2 T b L lo hi z pS nS s := by
  unfold TopPre0 at h; unfold TopPre; exact ⟨h30a, h30b, h⟩

end Fv256.Arm64.ScanSpec
