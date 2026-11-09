import Fv256.Spec.Arm64.FromHexLib
import Fv256.Spec.Arm64.SfdTopSpec
import Fv256.Spec.Arm64.UnmarshalSpec
import Fv256.Spec.I

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C

open Fv256.Arm64.SfdTopSpec Fv256.Arm64.UnmarshalSpec Fv256.Arm64.FromHexLib

namespace Fv256.Arm64.UnmarshalHex

variable (C : SfdCfg)

/-- the environment of the hex parser: the digit table and the package error variables (package-level data of the binary:
the table is read-only, the error variables are initialised interface values), outside the runtime-owned ranges and the
stack window and the receiver. -/
def HexEnv (R : RtInv) (lo hi : Nat) (z : BitVec 64) (s : State) : Prop :=
  (∀ c, c < 256 → s.mem.readLE (1002789 + c) 1 = (hexNib c).getD 255) ∧
  s.mem.accessible 1002789 256 false = true ∧
  Outside 1002789 256 [(lo, hi), (z.toNat, z.toNat + 32)] ∧ Outside 1002789 256 R.rt ∧
  s.mem.accessible 1792784 96 false = true ∧
  Outside 1792784 96 [(lo, hi), (z.toNat, z.toNat + 32)] ∧ Outside 1792784 96 R.rt ∧
  (∀ e, e < 6 → s.mem.readLE (errAddrOf e) 8 ≠ 0)

end Fv256.Arm64.UnmarshalHex
