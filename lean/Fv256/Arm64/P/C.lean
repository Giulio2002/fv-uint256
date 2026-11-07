import Fv256.Arm64.StrProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.DecMath
import Fv256.Arm64.P.T
import Fv256.Arm64.P.A

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI
open Fv256.E

namespace Fv256.Arm64.P

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem chunk_pre (s : State) (u : Nat) (hu : u < 2 ^ 64) (hu29 : 2 ^ 29 ≤ u)
    (hpc : s.pc = BitVec.ofNat 64 (fb + 0x28)) (e3 : s.regs 3 = BitVec.ofNat 64 u) :
    ReachesRet Fv256.Arm64.StrProg.program (BitVec.ofNat 64 (fb + 0x78)) s (fun S' =>
      S'.regs 3 = BitVec.ofNat 64 (u % 10 ^ 9) ∧ S'.regs 4 = BitVec.ofNat 64 (u / 10 ^ 9) ∧ S'.regs 6 = 0#64 ∧
      (∀ k, k ∉ [3, 4, 5, 6] → S'.regs k = s.regs k) ∧ S'.sp = s.sp ∧ S'.mem = s.mem) := by
  have hc : fb + 0x300 < 2 ^ 47 := by decide
  have h29 : (((BitVec.ofNat 64 u).rotateRight 29).toNat % 34359738368 = 0) = False := by
    apply eq_false
    intro h
    have := rot_lsr u 29 hu (by omega) (by omega)
    simp only [show 64 - 29 = 35 from rfl, show (2:Nat)^35 = 34359738368 from rfl] at this
    rw [this] at h
    have : 2 ^ 29 ≤ u := hu29
    have h2 := (Nat.div_eq_zero_iff).1 h
    omega
  have r1 := p1 u hu
  have r2 := p2 u hu
  have r3 := p3 u hu
  janus_run [e3, h29, r1, r2, r3] until [fb + 0x78]
  refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp [setReg]
  · simp [setReg]
  · simp [setReg]
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setReg, hk]
end Fv256.Arm64.P
