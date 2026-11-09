import Fv256.Spec.Amd64.FromDecimalSpec
import Fv256.Spec.Amd64.FromHexLib
import Fv256.Spec.Amd64.SfdTopSpec
import Fv256.Spec.Amd64.UnmarshalSpec
import Fv256.Spec.I

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C

open Fv256.Amd64.SfdTopSpec Fv256.Amd64.UnmarshalSpec Fv256.Amd64.FromHexLib

namespace Fv256.Amd64.UnmarshalHex

variable (C : SfdCfg)

/-- the environment of the hex parser: the digit table and the package error variables (package-level data of the binary:
the table is read-only, the error variables are initialised interface values), outside the runtime-owned ranges and the
stack window and the receiver. -/
def HexEnv (R : RtInv) (lo hi : Nat) (z : BitVec 64) (s : State) : Prop :=
  (∀ c, c < 256 → s.mem.readLE (5176782 + c) 1 = (hexNib c).getD 255) ∧
  s.mem.accessible 5176782 256 false = true ∧
  Outside 5176782 256 [(lo, hi), (z.toNat, z.toNat + 32)] ∧ Outside 5176782 256 R.rt ∧
  s.mem.accessible 5995344 96 false = true ∧
  Outside 5995344 96 [(lo, hi), (z.toNat, z.toNat + 32)] ∧ Outside 5995344 96 R.rt ∧
  (∀ e, e < 6 → s.mem.readLE (errAddrOf e) 8 ≠ 0)

/-- `input` starts with `0x` or `0X` -/
abbrev IsHex (m : Janus.Arm64.Memory) (p n : Nat) : Prop :=
  2 ≤ n ∧ m.readLE p 1 = 48 ∧ (m.readLE (p + 1) 1 = 120 ∨ m.readLE (p + 1) 1 = 88)

/-- `UnmarshalJSON`: the input is a quoted string (`n >= 2`, first and last byte `"`); the last byte is addressed as the
code does, `n + p - 1` -/
abbrev Quoted (m : Janus.Arm64.Memory) (p n : Nat) : Prop :=
  2 ≤ n ∧ m.readLE p 1 = 34 ∧ m.readLE (n + p - 1) 1 = 34

end Fv256.Amd64.UnmarshalHex
