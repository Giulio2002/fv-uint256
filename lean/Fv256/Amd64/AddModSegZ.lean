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

namespace Fv256.Amd64.AddModSegZ

abbrev addmodEntry : Nat := segAddr Fv256.AddModProg.program "github.com/holiman/uint256.(*Int).AddMod"

-- `0x235` with `m = 0`: zero `z`, epilogue, `ret`.
set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem segZ (S : State) (hpc : S.rip = BitVec.ofNat 64 (addmodEntry + 0x235))
    (hx15 : S.xmm 15 = 0) (hret : S.mem.readLE ((S.regs 4).toNat + 0x168) 8 < 2 ^ 47)
    (hacc : S.mem.accessible ((S.regs 4).toNat + 0x150) 0x20 true = true)
    (hnw : (S.regs 4).toNat + 0x170 ≤ 2 ^ 48)
    (hz : Buffer S (S.regs 0) 32 true) (hm : Buffer S (S.regs 7) 32 false)
    (hr2 : S.regs 2 = BitVec.ofNat 64 (S.mem.readLE ((S.regs 7).toNat + 24) 8))
    (hm0 : S.mem.readLE (S.regs 7).toNat 8 = 0 ∧ S.mem.readLE ((S.regs 7).toNat + 8) 8 = 0 ∧ S.mem.readLE ((S.regs 7).toNat + 16) 8 = 0 ∧ S.mem.readLE ((S.regs 7).toNat + 24) 8 = 0)
    (hdz : (S.regs 0).toNat + 32 ≤ (S.regs 4).toNat + 0x150 ∨ (S.regs 4).toNat + 0x170 ≤ (S.regs 0).toNat) :
    ReachesRet Fv256.AddModProg.program (BitVec.ofNat 64 (S.mem.readLE ((S.regs 4).toNat + 0x168) 8)) S
      (fun S' => S'.regs 0 = S.regs 0 ∧ S'.regs 4 = S.regs 4 + 0x170#64 ∧
        S'.regs 5 = BitVec.ofNat 64 (S.mem.readLE ((S.regs 4).toNat + 352) 8) ∧ S'.regs 14 = S.regs 14 ∧
        S'.xmm 15 = S.xmm 15 ∧ S'.df = S.df ∧ S'.mxcsr = S.mxcsr ∧
        S'.mem.readLE (S.regs 0).toNat 32 = 0 ∧
        MemFrame S.mem S'.mem [((S.regs 0).toNat, (S.regs 0).toNat + 32)]) := by
  obtain ⟨hzw, hza⟩ := hz
  obtain ⟨hmw, hma⟩ := hm
  obtain ⟨m0, m1, m2, m3⟩ := hm0
  janus64_run
  refine ⟨?_, ?_⟩
  · simp (disch := omega) [Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside, Janus.Arm64.Memory.readLE_writeLE_self]
  · janus_frame

end Fv256.Amd64.AddModSegZ
