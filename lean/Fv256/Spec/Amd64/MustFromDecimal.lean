import Extracted
import Fv256.Spec.Amd64.FromDecimalSpec
import Fv256.Spec.Amd64.SfdTopSpec
import Fv256.Spec.Core
import Fv256.Spec.I
import Fv256.Spec.SumC64
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Janus.Contracts.PanicAmd64 Fv256.I Fv256.C

open Fv256.Amd64.SfdTopSpec

namespace Fv256.Amd64.MustFromDecimal

/-- the `SfdCfg` of this binary -/
def cfg : SfdCfg :=
  (Extracted.dataAddr.«io.EOF»,
    Extracted.dataAddr.«github.com/holiman/uint256.ErrBig256Range»,
    Extracted.dataAddr.«github.com/holiman/uint256.multipliers»,
    Extracted.dataAddr.«type:strconv.NumError#3eb4e62e»,
    Extracted.dataAddr.«go:itab.*strconv.NumError,error»,
    Extracted.dataAddr.«go:itab.internal/strconv.Error,error»,
    Extracted.dataAddr.«.rodata#9967e7a3»,
    Extracted.dataAddr.«strconv.ErrSyntax»,
    Extracted.dataAddr.«runtime.writeBarrier»,
    Extracted.dataAddr.«.rodata#3d2a826c»,
    Extracted.dataAddr.«.rodata#575028b4»,
    Extracted.program.contractAddr "runtime.mallocgc",
    Extracted.program.contractAddr "runtime.memmove",
    Extracted.program.contractAddr "runtime.newobject",
    Extracted.program.contractAddr "runtime.gcWriteBarrier1",
    Extracted.program.contractAddr "runtime.gcWriteBarrier2")

open Fv256.C in
/-- precondition of `MustFromDecimal(s)` (string pointer in `RAX`, length in `RBX`): `FromDecimalSpec.PreC` plus the rodata and `PanicInit` -/
def PreFd (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (pS nS : BitVec 64) (s : State) : Prop :=
  Fv256.Amd64.FromDecimalSpec.PreC0 cfg R R2 T b L lo hi Extracted.dataAddr.«type:uint256.Int#33f34945» pS nS s ∧
  Extracted.program.DataLoaded s.mem ∧ Fv256.Amd64.FromDecimalSpec.PanicInit cfg R R2 lo hi s.mem

end Fv256.Amd64.MustFromDecimal
