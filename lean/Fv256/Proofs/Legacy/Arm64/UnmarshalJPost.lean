import Fv256.Spec.Arm64.UnmarshalHex
import Fv256.Spec.Arm64.UnmarshalSpecJ

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C

open Fv256.Arm64.SfdTopSpec Fv256.Arm64.FromHexLib Fv256.Arm64.UnmarshalPost Fv256.Arm64.UnmarshalSpecJ

namespace Fv256.Arm64.UnmarshalJPost

def JPost (C : SfdCfg) (R : RtInv) (R2 : IfaceModel) (lo hi : Nat) (z : BitVec 64) (p n : Nat) (s s' : State) : Prop :=
  (Quoted s.mem p n →
    (IsHex s.mem (p + 1) (n - 2) → HexPart z s.mem (p + 1) (n - 2) s') ∧
    (¬ IsHex s.mem (p + 1) (n - 2) → DecPart C z s.mem (p + 1) (n - 2) s')) ∧
  (¬ Quoted s.mem p n → DecPart C z s.mem p n s') ∧
  MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)])

end Fv256.Arm64.UnmarshalJPost
