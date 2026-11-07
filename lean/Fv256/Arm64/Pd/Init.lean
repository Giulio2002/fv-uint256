import Fv256.Arm64.PrettyProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.PdCells
import Fv256.Arm64.P.T
import Fv256.Arm64.P.A
import Fv256.UtilB2
import Fv256.Util
import Fv256.Arm64.Pd.Tabs

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec
open Fv256.E Fv256.Arm64.P Fv256.Arm64.Pd

namespace Fv256.Arm64.Pd

/-- Entry of `(*Int).PrettyDec` (arm64). -/
def pdE : Nat := segAddr Fv256.Arm64.PrettyProg.program "github.com/holiman/uint256.(*Int).PrettyDec"
/-- The loop head (`STR R0, 312(RSP)` after the receiver is copied), `0xfc` bytes into the function. -/
def pdH : Nat := pdE + 0xfc

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem pd_init (s : State) (hpc : s.pc = BitVec.ofNat 64 pdE) (zp : Nat) (e0 : s.regs 0 = BitVec.ofNat 64 zp)
    (hg : GuardOK s 272) (hal : s.sp.toNat % 16 = 0) (h408 : 0x300 ≤ s.sp.toNat) (hsp2 : s.sp.toNat < 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 0x300) (0x300 + 0x18) true = true)
    (hd : Fv256.Arm64.PrettyProg.program.DataLoaded s.mem)
    (hz : zp + 32 ≤ 2 ^ 48 ∧ s.mem.accessible zp 32 false = true)
    (hzd : zp + 32 ≤ s.sp.toNat - 0x300 ∨ s.sp.toNat + 0x18 ≤ zp)
    (hret : (s.regs 30).toNat < 2 ^ 48)
    (hv0 : s.mem.readLE zp 32 ≠ 0) :
    ReachesRet Fv256.Arm64.PrettyProg.program (BitVec.ofNat 64 pdH) s (fun S' => True) := by
  have hc : pdE + 0x400 < 2 ^ 47 := by decide
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hzn, hza⟩ := hz
  janus_data hd [hw]
  have l0 := Janus.Arm64.Memory.readLE_lt s.mem zp 8
  have l1 := Janus.Arm64.Memory.readLE_lt s.mem (zp + 8) 8
  have l2 := Janus.Arm64.Memory.readLE_lt s.mem (zp + 16) 8
  have l3 := Janus.Arm64.Memory.readLE_lt s.mem (zp + 24) 8
  simp only [Nat.reducePow] at l0 l1 l2 l3
  rw [Util.readLE_32] at hv0
  have hnz : ((BitVec.ofNat 64 (s.mem.readLE (zp + 8) 8) ||| BitVec.ofNat 64 (s.mem.readLE zp 8) |||
      BitVec.ofNat 64 (s.mem.readLE (zp + 16) 8) ||| BitVec.ofNat 64 (s.mem.readLE (zp + 24) 8)).toNat = 0) = False := by
    apply eq_false
    intro h
    rw [BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : s.mem.readLE zp 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 8) 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 16) 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 24) 8 < 2 ^ 64)] at h
    simp only [Nat.or_eq_zero_iff] at h
    omega
  janus_run [e0, hnz, Nat.or_eq_zero_iff] until [pdH]
  trace_state
  sorry
end Fv256.Arm64.Pd
