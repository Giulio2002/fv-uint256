import Extracted
import Fv256.SpecE
import Fv256.UtilE
import Fv256.Amd64.DecA

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Dec

set_option maxHeartbeats 8000000 in
theorem chunk_post_loop (s0 : State) (ptr len b lo ud : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hb : 1 ≤ b) (hbl : b ≤ len) (hlo : lo < 10) (hud : ud ≠ 0) (hud2 : ud < 2 ^ 64)
    (hp : ptr + len ≤ 2 ^ 48) (hacc : M.accessible ptr len true = true) (hd : Extracted.program.DataLoaded M)
    (e1 : R 1 = BitVec.ofNat 64 len) (e3 : R 3 = BitVec.ofNat 64 b) (e6 : R 6 = BitVec.ofNat 64 lo)
    (e2 : R 2 = BitVec.ofNat 64 ud) (e7 : R 7 = BitVec.ofNat 64 ptr) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (fb + 0x17))
      { s0 with regs := R, rip := BitVec.ofNat 64 (fb + 0xbe), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (fb + 0x17), flags := fl', mem := M' } ∧
        R' 0 = BitVec.ofNat 64 ptr ∧ R' 3 = BitVec.ofNat 64 (b - 1) ∧ R' 7 = BitVec.ofNat 64 ud ∧
        R' 1 = R 1 ∧ (∀ k, k ∉ [0, 2, 3, 6, 7, 8] → R' k = R k) ∧
        M'.readLE (ptr + b - 1) 1 = 48 + lo ∧ MemFrame M M' [(ptr + b - 1, ptr + b)] ∧
        Extracted.program.DataLoaded M') := by
  have hc : fb + 0x300 < 2 ^ 47 := by decide
  have hud0 : ¬ (BitVec.ofNat 64 ud = 0#64) := by
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hud2] at this
    exact hud this
  have hsr := smalls_read hd lo (by omega)
  janus64_data hd [hacc]
  janus64_run [e1, e3, e6, e2, e7, hud0] until [fb + 0x17]
  have hw : (b + (18446744073709551615 + ptr) % 18446744073709551616) % 18446744073709551616 = ptr + b - 1 := by omega
  have hk1 : ((lo + lo) % 4294967296 + 1) % 4294967296 + 5176582 = smallsBase + 2 * lo + 1 := by
    simp only [smallsBase]; omega
  simp only [smallsBase] at hsr
  rw [hw, hk1]
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setRegF]
  · simp [setRegF]; bv_omega
  · simp [setRegF]
  · simp [setRegF, e1]
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setRegF, hk]
  · rw [Janus.Arm64.Memory.readLE_writeLE_self, hsr.2]
    simp only [Nat.pow_one]; omega
  · exact MemFrame.of_writeLE M _ (r := (ptr + b - 1, ptr + b)) (List.mem_singleton_self _) (by omega) (by omega)
  · exact Fv256.E.dataLoaded_writeLE hd (accessible_sub hacc (Or.inr rfl) (by omega) (by omega)) _
set_option maxHeartbeats 8000000 in
theorem chunk_post_ret (s0 : State) (ptr len b lo ud : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hb : 1 ≤ b) (hbl : b ≤ len) (hlo : lo < 10) (hud : ud = 0)
    (hp : ptr + len ≤ 2 ^ 48) (hacc : M.accessible ptr len true = true) (hd : Extracted.program.DataLoaded M)
    (e1 : R 1 = BitVec.ofNat 64 len) (e3 : R 3 = BitVec.ofNat 64 b) (e6 : R 6 = BitVec.ofNat 64 lo)
    (e2 : R 2 = BitVec.ofNat 64 0) (e7 : R 7 = BitVec.ofNat 64 ptr) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (fb + 0x1b4))
      { s0 with regs := R, rip := BitVec.ofNat 64 (fb + 0xbe), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (fb + 0x1b4), flags := fl', mem := M' } ∧
        R' 0 = BitVec.ofNat 64 (b - 1) ∧ R' 3 = BitVec.ofNat 64 b ∧ R' 7 = BitVec.ofNat 64 ptr ∧
        R' 1 = R 1 ∧ (∀ k, k ∉ [0, 2, 3, 6, 7, 8] → R' k = R k) ∧
        M'.readLE (ptr + b - 1) 1 = 48 + lo ∧ MemFrame M M' [(ptr + b - 1, ptr + b)] ∧
        Extracted.program.DataLoaded M') := by
  have hc : fb + 0x300 < 2 ^ 47 := by decide
  subst hud
  have hsr := smalls_read hd lo (by omega)
  janus64_data hd [hacc]
  janus64_run [e1, e3, e6, e2, e7] until [fb + 0x1b4]
  have hw : (b + (18446744073709551615 + ptr) % 18446744073709551616) % 18446744073709551616 = ptr + b - 1 := by omega
  have hk1 : ((lo + lo) % 4294967296 + 1) % 4294967296 + 5176582 = smallsBase + 2 * lo + 1 := by
    simp only [smallsBase]; omega
  simp only [smallsBase] at hsr
  rw [hw, hk1]
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setRegF]; bv_omega
  · simp [setRegF, e3]
  · simp [setRegF, e7]
  · simp [setRegF, e1]
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setRegF, hk]
  · rw [Janus.Arm64.Memory.readLE_writeLE_self, hsr.2]
    simp only [Nat.pow_one]; omega
  · exact MemFrame.of_writeLE M _ (r := (ptr + b - 1, ptr + b)) (List.mem_singleton_self _) (by omega) (by omega)
  · exact Fv256.E.dataLoaded_writeLE hd (accessible_sub hacc (Or.inr rfl) (by omega) (by omega)) _
end Fv256.Amd64.Dec
