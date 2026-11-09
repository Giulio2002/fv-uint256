import Extracted
import Fv256.Spec.FormatFastDefs

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.IfaceAmd64

open Fv256.FormatFast

namespace Fv256.Amd64.FormatFast

/-- the answers the machine acted on when it left the query chain for the big path (first non-plain answer, or a verb outside `d v s x`) -/
def NotPlain (RW RP RF : Res) (data tab rW : BitVec 64) (fP fF ch : Nat) : Prop :=
  (∃ j3, WRes RW data tab rW j3 ∧ j3.toNat % 256 ≠ 0) ∨
  (∃ j3, (WRes RW data tab rW j3 ∧ j3.toNat % 256 = 0) ∧ PRes RP data j3 fP (fun j => j.toNat % 256 ≠ 0)) ∨
  (∃ j3, ((WRes RW data tab rW j3 ∧ j3.toNat % 256 = 0) ∧ PRes RP data j3 fP (fun j => j.toNat % 256 = 0)) ∧
    FRes RF data fF 0x2b (fun j => j.toNat % 256 ≠ 0)) ∨
  (∃ j3, (((WRes RW data tab rW j3 ∧ j3.toNat % 256 = 0) ∧ PRes RP data j3 fP (fun j => j.toNat % 256 = 0)) ∧
    FRes RF data fF 0x2b fz) ∧ FRes RF data fF 0x20 (fun j => j.toNat % 256 ≠ 0)) ∨
  (∃ j3, ((((WRes RW data tab rW j3 ∧ j3.toNat % 256 = 0) ∧ PRes RP data j3 fP (fun j => j.toNat % 256 = 0)) ∧
    FRes RF data fF 0x2b fz) ∧ FRes RF data fF 0x20 fz) ∧ FRes RF data fF 0x2d (fun j => j.toNat % 256 = 1)) ∨
  (∃ j3, (((((WRes RW data tab rW j3 ∧ j3.toNat % 256 = 0) ∧ PRes RP data j3 fP (fun j => j.toNat % 256 = 0)) ∧
    FRes RF data fF 0x2b fz) ∧ FRes RF data fF 0x20 fz) ∧ FRes RF data fF 0x2d fx) ∧
    FRes RF data fF 0x30 (fun j => j.toNat % 256 ≠ 0)) ∨
  (∃ j3, ((((((WRes RW data tab rW j3 ∧ j3.toNat % 256 = 0) ∧ PRes RP data j3 fP (fun j => j.toNat % 256 = 0)) ∧
    FRes RF data fF 0x2b fz) ∧ FRes RF data fF 0x20 fz) ∧ FRes RF data fF 0x2d fx) ∧ FRes RF data fF 0x30 fz) ∧
    FRes RF data fF 0x23 (fun j => j.toNat % 256 = 1)) ∨
  (∃ j3, PlainHist RW RP RF data tab rW j3 fP fF ∧ ch ≠ 100 ∧ ch ≠ 115 ∧ ch ≠ 118 ∧ ch ≠ 120)

end Fv256.Amd64.FormatFast
