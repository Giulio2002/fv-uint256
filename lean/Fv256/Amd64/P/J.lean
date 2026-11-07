import Fv256.StrProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.Amd64.P.A

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E

namespace Fv256.Amd64.P

/-- `formatBase10` loop head with `u < 2^29`: jump to the final chunk (`fb+0x109`), `DX = u`. -/
theorem to_final (s0 : State) (u : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hu : u < 2 ^ 29) (e7 : R 7 = BitVec.ofNat 64 u) :
    ReachesRet Fv256.StrProg.program (BitVec.ofNat 64 (fb + 0x109))
      { s0 with regs := R, rip := BitVec.ofNat 64 (fb + 0x17), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (fb + 0x109), flags := fl', mem := M } ∧
        R' 2 = BitVec.ofNat 64 u ∧ (∀ k, k ∉ [2, 7] → R' k = R k)) := by
  have hc : fb + 0x300 < 2 ^ 47 := by decide
  have h29 : (BitVec.ofNat 64 u >>> 29 = 0#64) = True := by
    apply eq_true
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
    have : u / 2 ^ 29 = 0 := Nat.div_eq_of_lt hu
    rw [this]; rfl
  have h29b : (BitVec.ofNat 64 u >>> 29 == 0#64) = true := by
    simpa using h29
  janus64_run [e7, h29, h29b]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · simp [setRegF]
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setRegF, hk]
end Fv256.Amd64.P
