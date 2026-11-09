import Fv256.Proofs.Common.DecProg
import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.UtilE
import Fv256.Proofs.Amd64.DecA
import Fv256.Proofs.Amd64.DecB

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Dec

theorem div1e9_nat (u : Nat) (h : u < 2^64) : 9903520314283042200 * (u / 2) / 18446744073709551616 / 268435456 = u / 1000000000 := by
  omega

theorem div1e9 (u : Nat) (h : u < 2^64) :
    (BitVec.ofNat 64 (9903520314283042200 * (BitVec.ofNat 64 u >>> 1).toNat / 18446744073709551616) >>> 28) = BitVec.ofNat 64 (u / 1000000000) := by
  apply BitVec.eq_of_toNat_eq
  have e1 : (BitVec.ofNat 64 u >>> 1).toNat = u / 2 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow]
  have h2 : 9903520314283042200 * (u / 2) / 18446744073709551616 < 2 ^ 64 := by omega
  rw [e1, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2,
    Nat.shiftRight_eq_div_pow]
  have := div1e9_nat u h
  rw [show (2:Nat)^28 = 268435456 by rfl, this]
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem mod1e9 (u : Nat) (h : u < 2^64) :
    BitVec.ofNat 64 u - BitVec.ofNat 64 (u / 1000000000) * 1000000000#64 = BitVec.ofNat 64 (u % 1000000000) := by
  apply BitVec.eq_of_toNat_eq
  have t1 : (BitVec.ofNat 64 u).toNat = u := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  have t2 : (BitVec.ofNat 64 (u / 1000000000)).toNat = u / 1000000000 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have t3 : (1000000000#64).toNat = 1000000000 := rfl
  have t4 : (BitVec.ofNat 64 (u % 1000000000)).toNat = u % 1000000000 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h3 : u / 1000000000 * 1000000000 < 2^64 := by omega
  rw [BitVec.toNat_sub, BitVec.toNat_mul, t1, t2, t3, t4, Nat.mod_eq_of_lt h3]
  omega

set_option maxHeartbeats 8000000 in
theorem chunk_pre (s0 : State) (u : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hu : u < 2 ^ 64) (hu29 : 2 ^ 29 ≤ u)
    (e7 : R 7 = BitVec.ofNat 64 u) :
    ReachesRet Fv256.DecProg.program (BitVec.ofNat 64 (fb + 0x60))
      { s0 with regs := R, rip := BitVec.ofNat 64 (fb + 0x17), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (fb + 0x60), flags := fl', mem := M } ∧
        R' 0 = 0#64 ∧ R' 3 = R 3 ∧ R' 1 = R 1 ∧ R' 7 = R 0 ∧ R' 6 = BitVec.ofNat 64 (u % 10 ^ 9) ∧
        R' 2 = BitVec.ofNat 64 (u / 10 ^ 9) ∧ (∀ k, k ∉ [0, 2, 6, 7, 8] → R' k = R k)) := by
  have hc : fb + 0x300 < 2 ^ 47 := by decide
  have h29 : (BitVec.ofNat 64 u >>> 29 = 0#64) = False := by
    apply eq_false
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu, Nat.shiftRight_eq_div_pow] at this
    simp at this
    omega
  have h29b : (BitVec.ofNat 64 u >>> 29 == 0#64) = false := by
    simpa using h29
  janus64_run [e7, h29, h29b]
  rw [div1e9 u hu, mod1e9 u hu]
  refine ⟨_, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try simp [setRegF])
  intro k h0 h2 h6 h7 h8
  simp [h0, h2, h6, h7, h8]

end Fv256.Amd64.Dec
