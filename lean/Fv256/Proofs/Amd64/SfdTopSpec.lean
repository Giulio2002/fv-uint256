import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecI
import Fv256.Proofs.Common.UtilI
import Fv256.Proofs.Common.SumC64
import Fv256.Proofs.Common.HexLemmas
import Fv256.Spec.Amd64.SfdTopSpec

/-!
# `(*Int).SetFromDecimal(s string) error` (amd64): the statement (Extracted-free)

Nothing here names an extraction.  Every binary-specific address (package variables, runtime type descriptors, runtime
entry points) is a field of `SfdCfg`; a consumer instantiates it for its own binary (the proof instantiates it with the
`Fv256.Amd64.SfdProg.dataAddr` / `contractAddr` values).  `TopPre`/`TopPost` are the Pre/Post of `Summary P entry (TopPre ..) (TopPost ..)`:
`z` in `RAX`, `s.ptr` in `RBX`, `s.len` in `RCX`; the `error` result is `RAX` (itab or type word) and `RBX` (data word), nil = `0, 0`.

The result is by cases on `Fv256.I.decParse` (the documented behaviour): the number (`ok v`: `z = v`, `err = nil`), `io.EOF`
(no digits left: `z = 0`), `ErrBig256Range` (too large: `z` unchanged), or the `*strconv.NumError{ParseUint, chunk, ErrSyntax}`
for the failing 19-digit chunk (`TeObj`, `z = 0`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I

namespace Fv256.Amd64.SfdTopSpec

/-- build a configuration from its 16 fields (in the order of the accessors) -/
def SfdCfg.mk (ioEOF : Nat) (errBig : Nat) (mulTab : Nat) (numErrType : Nat) (numErrItab : Nat) (errItab : Nat) (synConst : Nat) (strconvErrSyntax : Nat) (wbFlag : Nat) (fnStr : Nat) (maxStr : Nat) (mallocgc : Nat) (memmove : Nat) (newobject : Nat) (wb1 : Nat) (wb2 : Nat) : SfdCfg :=
  (ioEOF, errBig, mulTab, numErrType, numErrItab, errItab, synConst, strconvErrSyntax, wbFlag, fnStr, maxStr, mallocgc, memmove, newobject, wb1, wb2)

variable (C : SfdCfg)

open Fv256.C in
/-- The internal precondition (of `SfdSummary`): `TopPre0` plus the call-state facts `RetOK` (the caller establishes them).
The statement of the Extracted-level `Ensures` uses `TopPre0` only; `RetOK` is derived from `CallSetup` and the stack window. -/
def TopPre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s : State) : Prop :=
  RetOK s ∧ TopPre0 C R R2 T b L lo hi z pS nS s

/-- the statement of the summary of `SetFromDecimal` on a program `P` with entry `entry` -/
def SfdSummary (P : Janus.Amd64.Program) (entry : Nat) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) : Prop :=
  Summary P entry (TopPre C R R2 T b L lo hi z pS nS) (TopPost C R R2 T b L lo hi z pS nS)

end Fv256.Amd64.SfdTopSpec
