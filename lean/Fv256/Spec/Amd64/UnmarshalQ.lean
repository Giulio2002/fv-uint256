import Fv256.Spec.Amd64.FromDecimalSpec
import Fv256.Spec.Amd64.FromHexLib
import Fv256.Spec.Amd64.SfdTopSpec
import Fv256.Spec.Amd64.UnmarshalHex
import Fv256.Spec.Amd64.UnmarshalSpec
import Fv256.Spec.Core
import Fv256.Spec.I
import Fv256.Spec.SumC64
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C

open Fv256.Amd64.SfdTopSpec Fv256.Amd64.UnmarshalSpec Fv256.Amd64.UnmarshalHex Fv256.Amd64.FromHexLib

namespace Fv256.Amd64.UnmarshalQ

variable (C : SfdCfg)

/-- the extra facts the inner `UnmarshalText` call needs (its frame sits `80` bytes lower; the runtime contract accepts the
copy of the unquoted subslice `(pI + 1, nI - 2)` into the buffers of that frame) -/
def QPre (sb : Nat) (R : RtInv) (b lo : Nat) (pI nI : BitVec 64) (s : State) : Prop :=
  lo + 4984 ≤ (s.regs 4).toNat ∧
  R.ok sb [(s.regs 4).toNat - 152, pI.toNat + 1, nI.toNat - 2] ∧
  R.ok sb [(s.regs 4).toNat - 120, pI.toNat + 1, nI.toNat - 2] ∧
  roundupsize (nI.toNat - 2) true ≤ b ∧
  (∀ sl, 1 ≤ sl → sl ≤ 19 → sl ≤ nI.toNat - 2 → R.ok C.mallocgc [sl, 0, 0] ∧ (∀ q p, R.ok C.memmove [q, p, sl]) ∧
    blockSize sl true + blockSize 48 false ≤ b - roundupsize (nI.toNat - 2) true)

end Fv256.Amd64.UnmarshalQ
