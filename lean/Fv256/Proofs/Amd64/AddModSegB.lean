import Fv256.Proofs.Common.AddModProg
import Fv256.Proofs.Amd64.AddModSpecS
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Common.UtilF
import Fv256.Proofs.Common.CodeIn
import Fv256.Proofs.Common.SegCompose

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.AddModSpecS

namespace Fv256.Amd64.AddModSegB

abbrev addmodEntry : Nat := segAddr Fv256.AddModProg.program "github.com/holiman/uint256.(*Int).AddMod"

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem segB (S : State) (hpc : S.rip = BitVec.ofNat 64 (addmodEntry + 0x235))
    (hm : ¬ (S.mem.readLE (S.regs 7).toNat 8 = 0 ∧ S.mem.readLE ((S.regs 7).toNat + 8) 8 = 0 ∧ S.mem.readLE ((S.regs 7).toNat + 16) 8 = 0 ∧ S.mem.readLE ((S.regs 7).toNat + 24) 8 = 0))
    (hne : S.regs 7 ≠ S.regs 0)
    (hmw : (S.regs 7).toNat + 32 ≤ 2 ^ 48) (hma : S.mem.accessible (S.regs 7).toNat 32 false = true)
    (hr2 : S.regs 2 = BitVec.ofNat 64 (S.mem.readLE ((S.regs 7).toNat + 24) 8)) :
    ReachesRet Fv256.AddModProg.program (BitVec.ofNat 64 (addmodEntry + 0x296)) S
      (fun S' => S'.rip = BitVec.ofNat 64 (addmodEntry + 0x296) ∧ S'.regs 2 = S.regs 7 ∧
        (∀ i, i ≠ 2 → i ≠ 11 → S'.regs i = S.regs i) ∧ S'.xmm = S.xmm ∧ S'.df = S.df ∧ S'.mxcsr = S.mxcsr ∧ S'.mem = S.mem) := by
  have hne' : (S.regs 7).toNat ≠ (S.regs 0).toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
  janus64_run [hne', Nat.or_eq_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, BitVec.toNat_ofNat] until [addmodEntry + 0x296]
  all_goals (intro i h2 h11; simp [h2, h11])

end Fv256.Amd64.AddModSegB
