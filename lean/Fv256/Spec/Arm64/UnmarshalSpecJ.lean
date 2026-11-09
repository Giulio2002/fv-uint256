import Fv256.Spec.Arm64.SfdTopSpec
import Fv256.Spec.Arm64.UnmarshalSpec

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C

open Fv256.Arm64.SfdTopSpec Fv256.Arm64.UnmarshalSpec

namespace Fv256.Arm64.UnmarshalSpecJ

variable (C : SfdCfg)

/-- the input is a quoted string: `n ≥ 2`, first and last byte are `"` (the last byte is `input[n-1]`) -/
abbrev Quoted (m : Janus.Arm64.Memory) (p n : Nat) : Prop :=
  2 ≤ n ∧ m.readLE p 1 = 34 ∧ m.readLE (p + n - 1) 1 = 34

def PreU0J (sb st : Nat) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (z pI nI : BitVec 64) (s : State) : Prop :=
  (s.regs 0 = z) ∧
  (s.regs 1 = pI) ∧
  (s.regs 2 = nI) ∧
  (Mod C R R2 T L) ∧
  (Env C R R2 T b L lo hi s) ∧
  (lo + 4640 ≤ s.sp.toNat) ∧
  (s.sp.toNat + 24 ≤ hi) ∧
  (roundupsize nI.toNat true ≤ b) ∧
  (Outside st 2048 [(lo, hi)]) ∧
  (Outside st 2048 R.rt) ∧
  (Outside st 2048 R2.priv) ∧
  (Outside st 2048 [(z.toNat, z.toNat + 32)]) ∧
  (MultOK C z.toNat lo hi s.mem) ∧
  (Outside C.mulTab 40 R.rt) ∧
  (∀ k, 1 ≤ k → k ≤ 4 → Outside (s.mem.readLE (C.mulTab + 8 * k) 8) 32 R.rt) ∧
  (s.mem.accessible C.ioEOF 16 false = true) ∧
  (Outside C.ioEOF 16 [(lo, hi), (z.toNat, z.toNat + 32)]) ∧
  (Outside C.ioEOF 16 R.rt) ∧
  (s.mem.accessible C.errBig 16 false = true) ∧
  (Outside C.errBig 16 [(lo, hi), (z.toNat, z.toNat + 32)]) ∧
  (Outside C.errBig 16 R.rt) ∧
  (Fv256.Arm64.UnmarshalSpec.InitDone C R2 s.mem) ∧
  (s.mem.accessible C.maxStr 78 false = true) ∧
  (Outside C.maxStr 78 [(lo, hi), (z.toNat, z.toNat + 32)]) ∧
  (Outside C.maxStr 78 R.rt) ∧
  (∀ k, k < 78 → s.mem.readLE (C.maxStr + k) 1 = maxDigit k) ∧
  (Ptr32 s.mem z true) ∧
  (z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat) ∧
  (Outside z.toNat 32 R.rt ∨ InRanges z.toNat 32 L) ∧
  (Outside z.toNat 32 R2.priv) ∧
  (∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(z.toNat, z.toNat + 32)]) ∧
  ((s.regs 28).toNat + 16 + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 28).toNat + 16) ∧
  (Ptr s.mem pI nI.toNat false) ∧
  (pI.toNat + nI.toNat ≤ lo ∨ hi ≤ pI.toNat) ∧
  (∀ sl, 1 ≤ sl → sl ≤ 19 → sl ≤ nI.toNat → R.ok C.mallocgc [sl, 0, 0] ∧ (∀ q p, R.ok C.memmove [q, p, sl]) ∧ blockSize sl true + blockSize 48 false ≤ b - roundupsize nI.toNat true)

def PreJ (sb st : Nat) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (z pI nI : BitVec 64) (s : State) : Prop :=
  PreU0J C sb st R R2 T b L lo hi z pI nI s ∧
  (¬ Quoted s.mem pI.toNat nI.toNat →
    (R.ok sb [s.sp.toNat - 72, pI.toNat, nI.toNat]) ∧ (R.ok sb [s.sp.toNat - 40, pI.toNat, nI.toNat])) ∧
  (Quoted s.mem pI.toNat nI.toNat →
    (lo + 4720 ≤ s.sp.toNat) ∧
    (R.ok sb [s.sp.toNat - 152, pI.toNat + 1, nI.toNat - 2]) ∧
    (R.ok sb [s.sp.toNat - 120, pI.toNat + 1, nI.toNat - 2]) ∧
    (roundupsize (nI.toNat - 2) true ≤ b) ∧
    (∀ sl, 1 ≤ sl → sl ≤ 19 → sl ≤ nI.toNat - 2 → R.ok C.mallocgc [sl, 0, 0] ∧ (∀ q p, R.ok C.memmove [q, p, sl]) ∧
      blockSize sl true + blockSize 48 false ≤ b - roundupsize (nI.toNat - 2) true))

end Fv256.Arm64.UnmarshalSpecJ
