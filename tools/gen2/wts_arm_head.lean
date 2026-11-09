import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.WriteToSlice

set_option maxHeartbeats 64000000 in
theorem correctness (z d len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, d, len, cap]
      (fun s => GuardOK s 0 ∧ StackOK s 24 24 ∧ Ptr32 s.mem z false ∧ len.toNat < 2 ^ 48 ∧
        Ptr s.mem d len.toNat true ∧ Disjoint z.toNat 32 d.toNat len.toNat ∧
        Disjoint z.toNat 32 (s.sp.toNat - 24) 48 ∧ Disjoint d.toNat len.toNat (s.sp.toNat - 24) 48)
      (fun s s' => Spec.fromBE (fun i => s'.mem.readLE (d.toNat + i) 1) (min len.toNat 32) =
          val256 s.mem z.toNat % 2 ^ (8 * min len.toNat 32) ∧
        Util.OnlyWrites2 s.mem s'.mem d.toNat (min len.toNat 32) (s.sp.toNat - 24) 48) := by
  intro ret hret s hs hpre
  by_cases hl : len.toNat < 32
  · rcases (show len.toNat = 0 ∨ len.toNat = 1 ∨ len.toNat = 2 ∨ len.toNat = 3 ∨ len.toNat = 4 ∨ len.toNat = 5 ∨ len.toNat = 6 ∨ len.toNat = 7 ∨ len.toNat = 8 ∨ len.toNat = 9 ∨ len.toNat = 10 ∨ len.toNat = 11 ∨ len.toNat = 12 ∨ len.toNat = 13 ∨ len.toNat = 14 ∨ len.toNat = 15 ∨ len.toNat = 16 ∨ len.toNat = 17 ∨ len.toNat = 18 ∨ len.toNat = 19 ∨ len.toNat = 20 ∨ len.toNat = 21 ∨ len.toNat = 22 ∨ len.toNat = 23 ∨ len.toNat = 24 ∨ len.toNat = 25 ∨ len.toNat = 26 ∨ len.toNat = 27 ∨ len.toNat = 28 ∨ len.toNat = 29 ∨ len.toNat = 30 ∨ len.toNat = 31 by omega) with @@HKS@@
    all_goals sorry
  · sorry

end Fv256.Arm64.WriteToSlice
