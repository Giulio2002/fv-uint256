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

namespace Fv256.Amd64.AddModSegD

abbrev addmodEntry : Nat := segAddr Fv256.AddModProg.program "github.com/holiman/uint256.(*Int).AddMod"

set_option maxRecDepth 100000 in
theorem hcMod : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ModProg.program Fv256.AddModProg.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

-- `0x3e5` (after the non-overflowing add): `Mod(z, z, m')` then the epilogue and `ret`.
set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem segD (S : State) (hpc : S.rip = BitVec.ofNat 64 (addmodEntry + 0x3e5))
    (hx15 : S.xmm 15 = 0) (hret : S.mem.readLE ((S.regs 4).toNat + 360) 8 < 2 ^ 47)
    (hlow : 0x1e8 ≤ (S.regs 4).toNat) (hnw : (S.regs 4).toNat + 0x170 ≤ 2 ^ 48)
    (hacc : S.mem.accessible ((S.regs 4).toNat - 0x1e0) 0x350 true = true)
    (hgl : S.mem.accessible ((S.regs 14).toNat + 16) 8 false = true)
    (hgn : (S.regs 14).toNat + 16 + 8 ≤ 2 ^ 48)
    (hgb : S.mem.readLE ((S.regs 14).toNat + 16) 8 + 0x190 < (S.regs 4).toNat)
    (hz : Buffer S (S.regs 0) 32 true) (hm : Buffer S (S.regs 2) 32 false)
    (hdz : (S.regs 0).toNat + 32 ≤ (S.regs 4).toNat - 0x1e0 ∨ (S.regs 4).toNat + 0x170 ≤ (S.regs 0).toNat)
    (hdm : (S.regs 2).toNat + 32 ≤ (S.regs 4).toNat - 0x1e0 ∨ (S.regs 4).toNat + 0x8 ≤ (S.regs 2).toNat)
    (hdg : ((S.regs 14).toNat + 24 ≤ (S.regs 4).toNat - 0x1e0 ∨ (S.regs 4).toNat + 0x8 ≤ (S.regs 14).toNat + 16)) :
    ReachesRet Fv256.AddModProg.program (BitVec.ofNat 64 (S.mem.readLE ((S.regs 4).toNat + 360) 8)) S
      (fun S' => S'.regs 0 = S.regs 0 ∧ S'.regs 4 = S.regs 4 + 368#64 ∧
        S'.regs 5 = BitVec.ofNat 64 (S.mem.readLE ((S.regs 4).toNat + 352) 8) ∧ S'.regs 14 = S.regs 14 ∧
        S'.xmm 15 = S.xmm 15 ∧ S'.df = S.df ∧ S'.mxcsr = S.mxcsr ∧
        S'.mem.readLE (S.regs 0).toNat 32 = Fv256.B.modSpec (S.mem.readLE (S.regs 0).toNat 32) (S.mem.readLE (S.regs 2).toNat 32) ∧
        MemFrame S.mem S'.mem [((S.regs 0).toNat, (S.regs 0).toNat + 32), ((S.regs 4).toNat - 0x1e0, (S.regs 4).toNat + 8)]) := by
  obtain ⟨hzw, hza⟩ := hz
  obtain ⟨hmw, hma⟩ := hm
  janus64_run calls [Fv256.CodeIn.lib_summary hcMod Fv256.Amd64.ModSum.mod_summary]
  all_goals janus_frame

end Fv256.Amd64.AddModSegD
