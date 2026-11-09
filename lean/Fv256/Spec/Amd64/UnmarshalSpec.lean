import Fv256.Spec.Amd64.FromDecimalSpec
import Fv256.Spec.Amd64.SfdTopSpec
import Fv256.Spec.Core
import Fv256.Spec.I
import Fv256.Spec.SumC64
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C

open Fv256.Amd64.SfdTopSpec

namespace Fv256.Amd64.UnmarshalSpec

variable (C : SfdCfg)

/-- `PreU` without `RetOK` (the top-level statements must not bound `[RSP]`; `RetOK` is derived inside the proof, `PreU0.retOK`) -/
def PreU0 (sb st : Nat) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (z pI nI : BitVec 64) (s : State) : Prop :=
  (s.regs 0 = z) ∧
  (s.regs 3 = pI) ∧
  (s.regs 1 = nI) ∧
  (Mod C R R2 T L) ∧
  (Env C R R2 T b L lo hi s) ∧
  (lo + 4904 ≤ (s.regs 4).toNat) ∧
  ((s.regs 4).toNat + 24 ≤ hi) ∧
  (R.ok sb [(s.regs 4).toNat - 72, pI.toNat, nI.toNat]) ∧
  (R.ok sb [(s.regs 4).toNat - 40, pI.toNat, nI.toNat]) ∧
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
  (Fv256.Amd64.FromDecimalSpec.InitDone C R2 s.mem) ∧
  (s.mem.accessible C.maxStr 78 false = true) ∧
  (Outside C.maxStr 78 [(lo, hi), (z.toNat, z.toNat + 32)]) ∧
  (Outside C.maxStr 78 R.rt) ∧
  (∀ k, k < 78 → s.mem.readLE (C.maxStr + k) 1 = maxDigit k) ∧
  (Buffer s z 32 true) ∧
  (z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat) ∧
  (Outside z.toNat 32 R.rt ∨ InRanges z.toNat 32 L) ∧
  (Outside z.toNat 32 R2.priv) ∧
  (∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(z.toNat, z.toNat + 32)]) ∧
  ((s.regs 14).toNat + 16 + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 14).toNat + 16) ∧
  (Buffer s pI nI.toNat false) ∧
  (pI.toNat + nI.toNat ≤ lo ∨ hi ≤ pI.toNat) ∧
  (∀ sl, 1 ≤ sl → sl ≤ 19 → sl ≤ nI.toNat → R.ok C.mallocgc [sl, 0, 0] ∧ (∀ q p, R.ok C.memmove [q, p, sl]) ∧     blockSize sl true + blockSize 48 false ≤ b - roundupsize nI.toNat true)

/-- `PreU0` without the two outer `slicebytetostring` ok conjuncts (UnmarshalJSON: they are only needed on the unquoted paths); was: `PreU` without `RetOK` (the top-level statements must not bound `[RSP]`; `RetOK` is derived inside the proof, `PreU0.retOK`) -/
def PreU0m (sb st : Nat) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (z pI nI : BitVec 64) (s : State) : Prop :=
  (s.regs 0 = z) ∧
  (s.regs 3 = pI) ∧
  (s.regs 1 = nI) ∧
  (Mod C R R2 T L) ∧
  (Env C R R2 T b L lo hi s) ∧
  (lo + 4904 ≤ (s.regs 4).toNat) ∧
  ((s.regs 4).toNat + 24 ≤ hi) ∧
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
  (Fv256.Amd64.FromDecimalSpec.InitDone C R2 s.mem) ∧
  (s.mem.accessible C.maxStr 78 false = true) ∧
  (Outside C.maxStr 78 [(lo, hi), (z.toNat, z.toNat + 32)]) ∧
  (Outside C.maxStr 78 R.rt) ∧
  (∀ k, k < 78 → s.mem.readLE (C.maxStr + k) 1 = maxDigit k) ∧
  (Buffer s z 32 true) ∧
  (z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat) ∧
  (Outside z.toNat 32 R.rt ∨ InRanges z.toNat 32 L) ∧
  (Outside z.toNat 32 R2.priv) ∧
  (∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(z.toNat, z.toNat + 32)]) ∧
  ((s.regs 14).toNat + 16 + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 14).toNat + 16) ∧
  (Buffer s pI nI.toNat false) ∧
  (pI.toNat + nI.toNat ≤ lo ∨ hi ≤ pI.toNat) ∧
  (∀ sl, 1 ≤ sl → sl ≤ 19 → sl ≤ nI.toNat → R.ok C.mallocgc [sl, 0, 0] ∧ (∀ q p, R.ok C.memmove [q, p, sl]) ∧     blockSize sl true + blockSize 48 false ≤ b - roundupsize nI.toNat true)

/-- the outer `slicebytetostring` requests of the unquoted paths -/
def OkOut (sb : Nat) (R : RtInv) (pI nI : BitVec 64) (s : State) : Prop :=
  R.ok sb [(s.regs 4).toNat - 72, pI.toNat, nI.toNat] ∧ R.ok sb [(s.regs 4).toNat - 40, pI.toNat, nI.toNat]

end Fv256.Amd64.UnmarshalSpec
