import Janus
import Fv256.Spec.MsaCommon

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

open Janus.Arm64 (Memory)

namespace Fv256.Amd64.Msa

open Fv256.Msa

/-- The requests the runtime must accept: `m` blocks remain, the next one needs length `n` and the slice has capacity `c`
(a `growslice(p, n, c, 8, uint8)` call is made exactly when `c < n`; its result capacity is `growCap 1 true n c`).
The only request parameter that is not determined by the arguments is the old pointer `p`. -/
def Ready (R : RtInv) (ga u8 : Nat) : Nat → Nat → Nat → Prop
  | 0, _, _ => True
  | m + 1, n, c => (c < n → (∀ p, R.ok ga [p, n, c, 8, u8]) ∧ Ready R ga u8 m (n + 8) (growCap 1 true n c)) ∧
      (n ≤ c → Ready R ga u8 m (n + 8) c)

/-- The postcondition of `MarshalSSZAppend` (amd64): the result slice is `(RAX, RBX = len0 + 32, RCX)`, nil error
(`RDI = RSI = 0`), the new bytes are the little-endian encoding of `*z`, the old prefix is kept, and the memory/runtime
facts of the no-growth / growth cases. -/
def AppendPost (R : RtInv) (s s' : State) (z : BitVec 64) (dp len0 cap0 b0 : Nat) (L0 : List (Nat × Nat)) : Prop :=
  (s'.regs 3).toNat = len0 + 32 ∧ s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧ len0 + 32 ≤ (s'.regs 1).toNat ∧
  s'.mem.readLE ((s'.regs 0).toNat + len0) 32 = val256 s.mem z.toNat ∧
  (∀ i, i < len0 → s'.mem.bytes ((s'.regs 0).toNat + i) = s.mem.bytes (dp + i)) ∧
  (len0 + 32 ≤ cap0 → (s'.regs 0).toNat = dp ∧ (s'.regs 1).toNat = cap0 ∧
    R.inv b0 L0 (s.regs 14).toNat (view R.rt L0 s'.mem) ∧
    MemFrame s.mem s'.mem [(dp + len0, dp + len0 + 32), ((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24)]) ∧
  (cap0 < len0 + 32 → InRanges (s'.regs 0).toNat (s'.regs 1).toNat R.rt ∧
    (∃ b' L', R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧ InRanges (s'.regs 0).toNat (s'.regs 1).toNat L') ∧
    MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24), (dp + len0, dp + cap0)]))

end Fv256.Amd64.Msa
