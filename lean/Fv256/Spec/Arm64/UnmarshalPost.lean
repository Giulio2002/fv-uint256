import Fv256.Spec.Arm64.UnmarshalHex

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C

open Fv256.Arm64.SfdTopSpec Fv256.Arm64.FromHexLib

namespace Fv256.Arm64.UnmarshalPost

/-- `input` starts with `0x` or `0X` -/
abbrev IsHex (m : Janus.Arm64.Memory) (p n : Nat) : Prop :=
  2 ≤ n ∧ m.readLE p 1 = 48 ∧ (m.readLE (p + 1) 1 = 120 ∨ m.readLE (p + 1) 1 = 88)

/-- the documented results of the hex path, for the string `(p, n)` read in memory `m` -/
def HexPart (z : BitVec 64) (m : Janus.Arm64.Memory) (p n : Nat) (s' : State) : Prop :=
  (∀ v, parseHex (bytesAt m p) n = .ok v →
      s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
  (∀ e, parseHex (bytesAt m p) n = .error e →
      s'.regs 0 = BitVec.ofNat 64 (m.readLE (errAddrOf e) 8) ∧
      s'.regs 1 = BitVec.ofNat 64 (m.readLE (errAddrOf e + 8) 8))

/-- the documented results of the decimal path -/
def DecPart (C : SfdCfg) (z : BitVec 64) (m : Janus.Arm64.Memory) (p n : Nat) (s' : State) : Prop :=
  (∀ v, decParse (bytesAt m p) n = .ok v →
      s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
  (decParse (bytesAt m p) n = .eof →
      (s'.regs 0).toNat = m.readLE C.ioEOF 8 ∧ (s'.regs 1).toNat = m.readLE (C.ioEOF + 8) 8 ∧
      Janus.Spec.val256 s'.mem z.toNat = 0) ∧
  (decParse (bytesAt m p) n = .range →
      (s'.regs 0).toNat = m.readLE C.errBig 8 ∧ (s'.regs 1).toNat = m.readLE (C.errBig + 8) 8 ∧
      Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 m z.toNat) ∧
  (∀ lo' len', decParse (bytesAt m p) n = .syntax lo' len' →
      s'.regs 0 = BitVec.ofNat 64 C.numErrItab)

/-- `UnmarshalText` on the string `(p, n)`: hex or decimal result, and the memory frame -/
def UTPost (C : SfdCfg) (R : RtInv) (R2 : IfaceModel) (lo hi : Nat) (z : BitVec 64) (p n : Nat) (s s' : State) : Prop :=
  (IsHex s.mem p n → HexPart z s.mem p n s') ∧
  (¬ IsHex s.mem p n → DecPart C z s.mem p n s') ∧
  MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)])

end Fv256.Arm64.UnmarshalPost
