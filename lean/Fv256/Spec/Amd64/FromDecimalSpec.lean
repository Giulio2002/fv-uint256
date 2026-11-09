import Fv256.Spec.Amd64.SfdTopSpec
import Fv256.Spec.Core
import Fv256.Spec.I
import Fv256.Spec.SumC64
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C

open Fv256.Amd64.SfdTopSpec

namespace Fv256.Amd64.FromDecimalSpec

variable (C : SfdCfg)

/-- Package-initialisation facts about the sentinel error variables, a documented environment assumption (`io.EOF` and
`uint256.ErrBig256Range` are initialised interface values: nonzero itab and data words) and the well-formedness of the
interface model's private ranges.  None of it reads `[RSP]`. -/
def InitDone (R2 : IfaceModel) (m : Janus.Arm64.Memory) : Prop :=
  m.readLE C.ioEOF 8 ≠ 0 ∧ m.readLE (C.ioEOF + 8) 8 ≠ 0 ∧ m.readLE C.errBig 8 ≠ 0 ∧ m.readLE (C.errBig + 8) 8 ≠ 0 ∧
  (∀ r ∈ R2.priv, r.1 ≤ r.2)

/-- `MustFromDecimal` additionally reads the type word of the error's itab (`mov 8(%rax), %rax`) before it panics: the itab words
of the sentinel errors, and the `*strconv.NumError` itab, are readable static data outside the runtime's ranges and the window. -/
def PanicInit (R : RtInv) (R2 : IfaceModel) (lo hi : Nat) (m : Janus.Arm64.Memory) : Prop :=
  (∀ w, (w = m.readLE C.ioEOF 8 ∨ w = m.readLE C.errBig 8) →
    w + 16 ≤ 2 ^ 48 ∧ m.accessible (w + 8) 8 false = true ∧ Outside (w + 8) 8 R.rt ∧ Outside (w + 8) 8 [(lo, hi)]) ∧
  Outside C.numErrItab 16 R.rt ∧ Outside C.numErrItab 16 [(lo, hi)] ∧ Outside C.numErrItab 16 R2.priv ∧ m.accessible C.numErrItab 16 false = true

def PreC0 (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi tI : Nat) (pS nS : BitVec 64)
    (s : State) : Prop :=
  s.regs 0 = pS ∧ s.regs 3 = nS ∧ Mod C R R2 T L ∧
  Env C R R2 T b L lo hi s ∧ lo + 4848 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 24 ≤ hi ∧
  R.ok C.newobject [tI] ∧ blockSize 32 true ≤ b ∧
  MultOK C lo lo hi s.mem ∧ Outside C.mulTab 40 R.rt ∧
  (∀ k, 1 ≤ k → k ≤ 4 → Outside (s.mem.readLE (C.mulTab + 8 * k) 8) 32 R.rt) ∧
  s.mem.accessible C.ioEOF 16 false = true ∧ Outside C.ioEOF 16 [(lo, hi)] ∧ Outside C.ioEOF 16 R.rt ∧
  s.mem.accessible C.errBig 16 false = true ∧ Outside C.errBig 16 [(lo, hi)] ∧ Outside C.errBig 16 R.rt ∧
  InitDone C R2 s.mem ∧
  s.mem.accessible C.maxStr 78 false = true ∧ Outside C.maxStr 78 [(lo, hi)] ∧ Outside C.maxStr 78 R.rt ∧
  (∀ k, k < 78 → s.mem.readLE (C.maxStr + k) 1 = maxDigit k) ∧
  Buffer s pS nS.toNat false ∧ (pS.toNat + nS.toNat ≤ lo ∨ hi ≤ pS.toNat) ∧
  (Outside pS.toNat nS.toNat R.rt ∨ InRanges pS.toNat nS.toNat L) ∧
  ChunkAll C R R2 L (b - blockSize 32 true) pS.toNat nS.toNat lo hi s.mem

end Fv256.Amd64.FromDecimalSpec
