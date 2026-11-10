import Janus
import Fv256.Spec.Basic
import Fv256.Spec.Add   -- `Fv256.Spec.add` lives in its own pure file
import Fv256.Spec.AddOverflow
import Fv256.Spec.AddUint64
import Fv256.Spec.Sub
import Fv256.Spec.SubOverflow
import Fv256.Spec.SubUint64
import Fv256.Spec.Neg
import Fv256.Spec.Abs
import Fv256.Spec.Not
import Fv256.Spec.And
import Fv256.Spec.Or
import Fv256.Spec.Xor
import Fv256.Spec.Clear
import Fv256.Spec.Set
import Fv256.Spec.SetOne
import Fv256.Spec.SetAllOne
import Fv256.Spec.SetUint64
import Fv256.Spec.Lsh
import Fv256.Spec.Rsh
import Fv256.Spec.SRsh
import Fv256.Spec.ExtendSign
import Fv256.Spec.SizeSSZ   -- `Fv256.Spec.sizeSSZ` lives in its own pure file
import Fv256.Spec.Mul   -- `Fv256.Spec.mul` likewise
import Fv256.Spec.IsZero
import Fv256.Spec.Eq
import Fv256.Spec.Lt
import Fv256.Spec.Gt
import Fv256.Spec.Cmp
import Fv256.Spec.Uint64
import Fv256.Spec.IsUint64
import Fv256.Spec.Sign
import Fv256.Spec.Signed
import Fv256.Spec.Slt
import Fv256.Spec.Sgt
import Fv256.Spec.Uint64WithOverflow
import Fv256.Spec.BitLen
import Fv256.Spec.ByteLen
import Fv256.Spec.Byte

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


namespace Fv256.Spec


/-- The big-endian value of the first `n` bytes of the byte sequence `f` (`f 0` is the most significant). -/
def fromBE (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => f 0 * 256 ^ n + fromBE (fun i => f (i + 1)) n


end Fv256.Spec
