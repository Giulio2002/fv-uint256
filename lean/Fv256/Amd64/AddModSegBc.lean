import Fv256.AddModProg
import Fv256.Amd64.AddModSpecS
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecF
import Fv256.UtilF
import Fv256.CodeIn
import Fv256.SegCompose
import Fv256.ChainProg
import Fv256.ModProg
import Fv256.Amd64.UdivremL
import Fv256.Amd64.ModSum

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.AddModSpecS

namespace Fv256.Amd64.AddModSegBc

abbrev addmodEntry : Nat := segAddr Fv256.AddModProg.program "github.com/holiman/uint256.(*Int).AddMod"

-- `0x235` with `m ≠ 0` and `m = z` (aliased): clone `m` onto the stack, continue at `0x296`.
set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem segBc (S : State) (hpc : S.rip = BitVec.ofNat 64 (addmodEntry + 0x235))
    (hm : ¬ (S.mem.readLE (S.regs 7).toNat 8 = 0 ∧ S.mem.readLE ((S.regs 7).toNat + 8) 8 = 0 ∧ S.mem.readLE ((S.regs 7).toNat + 16) 8 = 0 ∧ S.mem.readLE ((S.regs 7).toNat + 24) 8 = 0))
    (hne : S.regs 7 = S.regs 0)
    (hx15 : S.xmm 15 = 0)
    (hmw : (S.regs 7).toNat + 32 ≤ 2 ^ 48) (hma : S.mem.accessible (S.regs 7).toNat 32 false = true)
    (hsa : S.mem.accessible ((S.regs 4).toNat + 0x140) 32 true = true) (hsw : (S.regs 4).toNat + 0x160 ≤ 2 ^ 48)
    (hdm : (S.regs 7).toNat + 32 ≤ (S.regs 4).toNat + 0x140 ∨ (S.regs 4).toNat + 0x160 ≤ (S.regs 7).toNat)
    (hr2 : S.regs 2 = BitVec.ofNat 64 (S.mem.readLE ((S.regs 7).toNat + 24) 8)) :
    ReachesRet Fv256.AddModProg.program (BitVec.ofNat 64 (addmodEntry + 0x296)) S
      (fun S' => S'.rip = BitVec.ofNat 64 (addmodEntry + 0x296) ∧ S'.regs 2 = S.regs 4 + 0x140#64 ∧
        (∀ i, i ≠ 2 → i ≠ 11 → S'.regs i = S.regs i) ∧ S'.xmm = S.xmm ∧ S'.df = S.df ∧ S'.mxcsr = S.mxcsr ∧
        MemFrame S.mem S'.mem [((S.regs 4).toNat + 0x140, (S.regs 4).toNat + 0x160)] ∧
        S'.mem.readLE ((S.regs 4).toNat + 0x140) 32 = S.mem.readLE (S.regs 7).toNat 32) := by
  rw [hne] at hm hmw hma hdm hr2 ⊢
  janus64_run [Nat.or_eq_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, BitVec.toNat_ofNat] until [addmodEntry + 0x296]
  refine ⟨fun i h2 h11 => by simp [h2, h11], ?_, ?_⟩
  · janus_frame
  · simp (disch := omega) [Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]

end Fv256.Amd64.AddModSegBc
