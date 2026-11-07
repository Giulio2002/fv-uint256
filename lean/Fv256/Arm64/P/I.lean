import Fv256.Arm64.StrProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.Arm64.P.T
import Fv256.Arm64.P.A

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI
open Fv256.E

namespace Fv256.Arm64.P

set_option maxHeartbeats 8000000 in
/-- The epilogue (`MOVD R1, R0; LDR R29; LDP.P R30; RET`), shared by `fb+0x1cc` and `fb+0x1ec`. -/
theorem tail_ret (s : State) (pcv bp ret : Nat) (hpc : pcv = fb + 0x1cc ∨ pcv = fb + 0x1ec)
    (hspc : s.pc = BitVec.ofNat 64 pcv) (hal : s.sp.toNat % 16 = 0) (h8 : 8 ≤ s.sp.toNat) (hsp2 : s.sp.toNat + 16 < 2 ^ 48)
    (hacc : s.mem.accessible (s.sp.toNat - 8) 16 false = true)
    (m0 : s.mem.readLE (s.sp.toNat - 8) 8 = bp) (m1 : s.mem.readLE s.sp.toNat 8 = ret)
    (hl : s.regs 30 = BitVec.ofNat 64 ret) (hret : ret < 2 ^ 48) (hret4 : ret % 4 = 0) :
    ReachesRet Fv256.Arm64.StrProg.program (BitVec.ofNat 64 ret) s (fun S' =>
      S'.regs 0 = s.regs 1 ∧ S'.sp = s.sp + 16#64 ∧ S'.regs 29 = BitVec.ofNat 64 bp ∧
      (∀ k, k ∉ [0, 29, 30] → S'.regs k = s.regs k) ∧ S'.mem = s.mem) := by
  have hc : fb + 0x300 < 2 ^ 47 := by decide
  rcases hpc with rfl | rfl
  all_goals (
    janus_run [m0, m1]
    all_goals (intro k hk
               simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
               simp [hk.1, hk.2.1, hk.2.2]))
end Fv256.Arm64.P
