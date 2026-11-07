import Fv256.StrProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.Amd64.P.A

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E

namespace Fv256.Amd64.P

/-- `MOVQ SI, AX; POPQ BP; RET` (`fb+0x199`). -/
theorem tail199 (s0 : State) (sp bp ret : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hsp : sp + 16 ≤ 2 ^ 48) (hacc : M.accessible sp 16 false = true)
    (e4 : R 4 = BitVec.ofNat 64 sp) (m0 : M.readLE sp 8 = bp) (m1 : M.readLE (sp + 8) 8 = ret)
    (hret : ret < 2 ^ 47) :
    ReachesRet Fv256.StrProg.program (BitVec.ofNat 64 ret)
      { s0 with regs := R, rip := BitVec.ofNat 64 (fb + 0x199), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 ret, flags := fl', mem := M } ∧
        R' 0 = R 6 ∧ R' 4 = BitVec.ofNat 64 (sp + 16) ∧ R' 5 = BitVec.ofNat 64 bp ∧
        (∀ k, k ∉ [0, 4, 5] → R' k = R k)) := by
  have hc : fb + 0x300 < 2 ^ 47 := by decide
  janus64_run [e4, m0, m1]
  refine ⟨_, _, rfl, ?_, ?_, ?_, ?_⟩
  · simp [setRegF]
  · simp [setRegF]; exact (BitVec.ofNat_add sp 16).symm
  · simp [setRegF]
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setRegF, hk]
/-- `POPQ BP; RET` (`fb+0x1b4`). -/
theorem tail1b4 (s0 : State) (sp bp ret : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hsp : sp + 16 ≤ 2 ^ 48) (hacc : M.accessible sp 16 false = true)
    (e4 : R 4 = BitVec.ofNat 64 sp) (m0 : M.readLE sp 8 = bp) (m1 : M.readLE (sp + 8) 8 = ret)
    (hret : ret < 2 ^ 47) :
    ReachesRet Fv256.StrProg.program (BitVec.ofNat 64 ret)
      { s0 with regs := R, rip := BitVec.ofNat 64 (fb + 0x1b4), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 ret, flags := fl', mem := M } ∧
        R' 4 = BitVec.ofNat 64 (sp + 16) ∧ R' 5 = BitVec.ofNat 64 bp ∧
        (∀ k, k ∉ [4, 5] → R' k = R k)) := by
  have hc : fb + 0x300 < 2 ^ 47 := by decide
  janus64_run [e4, m0, m1]
  refine ⟨_, _, rfl, ?_, ?_, ?_⟩
  · simp [setRegF]; exact (BitVec.ofNat_add sp 16).symm
  · simp [setRegF]
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setRegF, hk]
end Fv256.Amd64.P
