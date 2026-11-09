import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecI
import Fv256.Proofs.Common.UtilI
import Fv256.Proofs.Common.SumC64
import Fv256.Proofs.Common.SpecScan
import Fv256.Proofs.Common.IndexByteSpec
import Fv256.Proofs.Amd64.SfdTopSpec
import Fv256.Proofs.Amd64.SfdEnvC
import Fv256.Proofs.Amd64.FromDecimalSpec
import Fv256.Spec.Amd64.ScanSpec

/-!
# `(*Int).Scan(src any) error` (amd64): the statement (Extracted-free)

`dst` in `RAX`, the dynamic type word of `src` in `RBX`, the data word in `RCX`.  Plain defs only (the audit rejects consumer
structures).  The three runtime types are `string` (`tyS`), `[]byte` (`tyB`); the dynamic cases are decided by the type word:
`0` (nil), `tyS`, `tyB`, anything else (`unsupported type`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.ScanSpec

namespace Fv256.Amd64.ScanSpec

variable (C : SfdCfg)

/-- precondition of `scanScientificFromString(dst, s)` at its entry (`dst` in `RAX`, `s.ptr` in `RBX`, `s.len` in `RCX`): the
`SetFromDecimal` precondition plus the frame (`0x70` bytes and the return slot below the entry `SP`, so `SetFromDecimal` sees
`lo + 4800 <= SP - 0x78`), the readability of `internal/cpu.X86.HasAVX2` and the pages of the string. -/
def SciPre (avx : Nat) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (dst p n : BitVec 64)
    (s : State) : Prop :=
  RetOK s ∧ TopPre0 C R R2 T b L lo hi dst p n s ∧ lo + 4920 ≤ (s.regs 4).toNat ∧ s.mem.accessible avx 1 false = true ∧
  Fv256.IndexByte.PageReadable s.mem p.toNat n.toNat ∧ (TlsG s ∧ Outside (s.fsBase.toNat - 8) 8 [(lo, hi)] ∧ Fv256.Amd64.FromDecimalSpec.InitDone C R2 s.mem)

/-- postcondition of `scanScientificFromString` -/
def SciPost (R : RtInv) (R2 : IfaceModel) (b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (dst p n : BitVec 64)
    (s s' : State) : Prop :=
  Kept s s' ∧ ScanStrPost C R b L lo hi dst p n s s' ∧
  MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)])

end Fv256.Amd64.ScanSpec
