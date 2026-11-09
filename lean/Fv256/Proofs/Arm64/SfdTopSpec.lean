import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecI
import Fv256.Proofs.Common.UtilI
import Fv256.Proofs.Common.HexLemmas
import Fv256.Spec.Arm64.SfdTopSpec

/-!
# `(*Int).SetFromDecimal(s string) error` (arm64): the statement (Extracted-free)

Nothing here names an extraction.  Every binary-specific address (package variables, runtime type descriptors, runtime
entry points) is a field of `SfdCfg`; a consumer instantiates it for its own binary (the proof instantiates it with the
`Extracted.dataAddr` / `contractAddr` values).  `TopPre`/`TopPost` are the Pre/Post of `Summary P entry (TopPre ..) (TopPost ..)`:
`z` in `X0`, `s.ptr` in `X1`, `s.len` in `X2`; the `error` result is `X0` (itab or type word) and `X1` (data word), nil = `0, 0`.

The result is by cases on `Fv256.I.decParse` (the documented behaviour): the number (`ok v`: `z = v`, `err = nil`), `io.EOF`
(no digits left: `z = 0`), `ErrBig256Range` (too large: `z` unchanged), or the `*strconv.NumError{ParseUint, chunk, ErrSyntax}`
for the failing 19-digit chunk (`TeObj`, `z = 0`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I

namespace Fv256.Arm64.SfdTopSpec

variable (C : SfdCfg)

/-- the statement of the summary of `SetFromDecimal` on a program `P` with entry `entry` -/
def SfdSummary (P : Janus.Program) (entry : Nat) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) : Prop :=
  Summary P entry (TopPre C R R2 T b L lo hi z pS nS) (TopPost C R R2 T b L lo hi z pS nS)

end Fv256.Arm64.SfdTopSpec
