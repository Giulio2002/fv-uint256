import Fv256.StrProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.Amd64.P.A

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.P

set_option maxHeartbeats 8000000 in
/-- One iteration of the final-chunk loop of `formatBase10` (`lo ≥ 100`, head `fb+0x109`): two digits. -/
theorem fin_step (s0 : State) (ptr len lo i : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hlo : 100 ≤ lo) (hlo2 : lo < 2 ^ 29) (hi : 2 ≤ i) (hil : i ≤ len)
    (hp : ptr + len ≤ 2 ^ 48) (hacc : M.accessible ptr len true = true)
    (e0 : R 0 = BitVec.ofNat 64 ptr) (e3 : R 3 = BitVec.ofNat 64 i) (e1 : R 1 = BitVec.ofNat 64 len)
    (e2 : R 2 = BitVec.ofNat 64 lo) (hd : TabsOK M) :
    ReachesRet Fv256.StrProg.program (BitVec.ofNat 64 (fb + 0x109))
      { s0 with regs := R, rip := BitVec.ofNat 64 (fb + 0x109), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (fb + 0x109), flags := fl', mem := M' } ∧
        R' 0 = BitVec.ofNat 64 ptr ∧ R' 3 = BitVec.ofNat 64 (i - 2) ∧ R' 1 = BitVec.ofNat 64 len ∧
        R' 2 = BitVec.ofNat 64 (lo / 100) ∧ (∀ k, k ∉ [2, 3, 6, 7, 8, 9] → R' k = R k) ∧
        M'.readLE (ptr + i - 2) 1 = 48 + lo % 100 / 10 ∧ M'.readLE (ptr + i - 1) 1 = 48 + lo % 10 ∧
        MemFrame M M' [(ptr + i - 2, ptr + i)] ∧ TabsOK M') := by
  have hc : fb + 0x300 < 2 ^ 47 := by decide
  have h9 : 2 ^ 29 < 2 ^ 32 := by decide
  have hx : lo < 2 ^ 32 := by omega
  have hq64 := div100_64 (BitVec.ofNat 64 lo) (by rw [BitVec.toNat_ofNat]; omega)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hq64
  have hq : BitVec.setWidth 32 (BitVec.ofNat 64 (lo / 100)) = BitVec.ofNat 32 (lo / 100) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : lo / 100 < 2^64)]
  have hm : (BitVec.ofNat 32 (lo / 100) * 100#32).toNat = 100 * (lo / 100) := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
    have : (100#32).toNat = 100 := rfl
    rw [this]
    rw [Nat.mod_eq_of_lt (by omega : lo / 100 < 2^32)]
    rw [Nat.mod_eq_of_lt (by omega : lo / 100 * 100 < 2^32)]
    omega
  tabs_data hd [hacc]
  janus64_run [e0, e3, e1, e2, hq, hq64] until [fb + 0x109]
  have hd2 : (4294967296 - (BitVec.ofNat 32 (lo / 100) * 100#32).toNat % 4294967296 + lo % 4294967296) % 4294967296 = lo % 100 := by
    rw [hm]; omega
  have hk0 : (lo % 100 + lo % 100) % 4294967296 = 2 * (lo % 100) := by omega
  have hk1 : (2 * (lo % 100) + 1) % 4294967296 + 5176582 = 5176582 + 2 * (lo % 100) + 1 := by
    omega
  have hw0 : (i + (18446744073709551614 + ptr) % 18446744073709551616) % 18446744073709551616 = ptr + i - 2 := by omega
  have hw1 : (i + (18446744073709551615 + ptr) % 18446744073709551616) % 18446744073709551616 = ptr + i - 1 := by omega
  have hsr := hd.smalls (lo % 100) (by omega)
  simp only [hd2, hk0, hk1]
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setRegF, e0]
  · simp only [setRegF]; simp; exact Fv256.E.ofNat_sub_ofNat i 2 (by omega) (by omega)
  · simp [setRegF, e1]
  · simp [setRegF]
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setRegF, hk]
  · simp only [hw0, hw1]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
      hsr.1]
    simp only [Nat.pow_one]; omega
  · simp only [hw0, hw1]
    rw [Janus.Arm64.Memory.readLE_writeLE_self, hsr.2]
    simp only [Nat.pow_one]; omega
  · simp only [hw0, hw1]
    exact ((MemFrame.refl M [(ptr + i - 2, ptr + i)]).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
      (List.mem_singleton_self _) (by omega) (by omega)
  · exact TabsOK.writeLE (TabsOK.writeLE hd (accessible_sub hacc (Or.inr rfl) (by omega) (by omega)) _) (by simp only [Janus.Arm64.Memory.accessible_writeLE]; exact accessible_sub hacc (Or.inr rfl) (by omega) (by omega)) _
end Fv256.Amd64.P
