import Extracted
import Fv256.SpecE
import Fv256.UtilE
import Fv256.Amd64.DecT
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
namespace Fv256.Amd64.Dec
theorem div100_nat (a : Nat) (h : a < 2^32) : a / 2 * 2748779070 / 137438953472 = a / 100 := by
  omega
theorem div100_64 (X : BitVec 64) (h : X.toNat < 2^32) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 X) >>> 1 * 2748779070#64) >>> 37 = BitVec.ofNat 64 (X.toNat / 100) := by
  apply BitVec.eq_of_toNat_eq
  have e1 : (BitVec.setWidth 64 (BitVec.setWidth 32 X) >>> 1).toNat = X.toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega : X.toNat < 2^32), Nat.mod_eq_of_lt (by omega : X.toNat < 2^64)]
  have e2 : (2748779070#64).toNat = 2748779070 := by rfl
  have h2 := div100_nat X.toNat h
  have h3 : X.toNat / 2 * 2748779070 < 2^64 := by omega
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, e1, e2, Nat.mod_eq_of_lt h3,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have : X.toNat / 2 * 2748779070 / 2 ^ 37 = X.toNat / 100 := by simpa using h2
  rw [this]
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem div100 (X : BitVec 64) (h : X.toNat < 2^32) :
    BitVec.setWidth 32 ((BitVec.setWidth 64 (BitVec.setWidth 32 X) >>> 1 * 2748779070#64) >>> 37) = BitVec.ofNat 32 (X.toNat / 100) := by
  rw [div100_64 X h]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : X.toNat / 100 < 2^32 := by omega
  rw [Nat.mod_eq_of_lt (by omega : X.toNat / 100 < 2^64)]

abbrev fb : Nat := segAddr Extracted.program "internal/strconv.formatBase10"

def Written (M : Memory) (ptr i0 lo c : Nat) : Prop :=
  ∀ k, k < c → M.readLE (ptr + i0 - 1 - k) 1 = 48 + lo / 10 ^ k % 10

set_option maxHeartbeats 8000000 in
theorem inner_step (s0 : State) (ptr len x i j : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hj : j < 4) (hi : 2 ≤ i) (hil : i ≤ len) (hlo : x < 10 ^ 9)
    (hp : ptr + len ≤ 2 ^ 48) (hacc : M.accessible ptr len true = true)
    (e0 : R 0 = BitVec.ofNat 64 j) (e3 : R 3 = BitVec.ofNat 64 i) (e1 : R 1 = BitVec.ofNat 64 len)
    (e7 : R 7 = BitVec.ofNat 64 ptr) (e6 : R 6 = BitVec.ofNat 64 x)
    (hd : TabsOK M) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (fb + 0x60))
      { s0 with regs := R, rip := BitVec.ofNat 64 (fb + 0x60), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (fb + 0x60), flags := fl', mem := M' } ∧
        R' 0 = BitVec.ofNat 64 (j + 1) ∧ R' 3 = BitVec.ofNat 64 (i - 2) ∧ R' 6 = BitVec.ofNat 64 (x / 100) ∧
        (∀ k, k ∉ [0, 3, 6, 8, 9, 10, 11] → R' k = R k) ∧
        M'.readLE (ptr + i - 2) 1 = 48 + x % 100 / 10 ∧ M'.readLE (ptr + i - 1) 1 = 48 + x % 100 % 10 ∧
        MemFrame M M' [(ptr + i - 2, ptr + i)] ∧ TabsOK M') := by
  have hc : fb + 0x300 < 2 ^ 47 := by decide
  have h9 : 10 ^ 9 < 2 ^ 32 := by decide
  have hx : x < 2 ^ 32 := by omega
  have hq : BitVec.setWidth 32 (BitVec.ofNat 64 (x / 100)) = BitVec.ofNat 32 (x / 100) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : x / 100 < 2^64)]
  have hq64 := div100_64 (BitVec.ofNat 64 x) (by rw [BitVec.toNat_ofNat]; omega)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hq64
  have hm : (BitVec.ofNat 32 (x / 100) * 100#32).toNat = 100 * (x / 100) := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
    have : (100#32).toNat = 100 := rfl
    rw [this]
    rw [Nat.mod_eq_of_lt (by omega : x / 100 < 2^32)]
    rw [Nat.mod_eq_of_lt (by omega : x / 100 * 100 < 2^32)]
    omega
  have hjj : (BitVec.ofNat 64 j).toNat = j := by simp; omega
  tabs_data hd [hacc]
  janus64_run [e0, e3, e1, e7, e6, hq, hq64] until [fb + 0x60]
  have hd2 : (4294967296 - (BitVec.ofNat 32 (x / 100) * 100#32).toNat % 4294967296 + x % 4294967296) % 4294967296 = x % 100 := by
    rw [hm]; omega
  have hk0 : (x % 100 + x % 100) % 4294967296 = 2 * (x % 100) := by omega
  have hk1 : (2 * (x % 100) + 1) % 4294967296 + 5176582 = 5176582 + 2 * (x % 100) + 1 := by
    omega
  have hw0 : (i + (18446744073709551614 + ptr) % 18446744073709551616) % 18446744073709551616 = ptr + i - 2 := by omega
  have hw1 : (i + (18446744073709551615 + ptr) % 18446744073709551616) % 18446744073709551616 = ptr + i - 1 := by omega
  have hsr := hd.smalls (x % 100) (by omega)
  simp only [hd2, hk0, hk1]
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setRegF] <;> try bv_omega
  · simp [setRegF] <;> try bv_omega
  · simp [setRegF]
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setRegF, hk]
  · simp only [hw0, hw1]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
      hsr.1]
    simp only [Nat.pow_one]; omega
  · simp only [hw0, hw1]
    rw [show ptr + i - 1 = ptr + i - 1 from rfl, Janus.Arm64.Memory.readLE_writeLE_self, hsr.2]
    simp only [Nat.pow_one]; omega
  · simp only [hw0, hw1]
    exact ((MemFrame.refl M [(ptr + i - 2, ptr + i)]).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
      (List.mem_singleton_self _) (by omega) (by omega)
  · exact TabsOK.writeLE (TabsOK.writeLE hd (accessible_sub hacc (Or.inr rfl) (by omega) (by omega)) _) (by simp only [Janus.Arm64.Memory.accessible_writeLE]; exact accessible_sub hacc (Or.inr rfl) (by omega) (by omega)) _

end Fv256.Amd64.Dec
