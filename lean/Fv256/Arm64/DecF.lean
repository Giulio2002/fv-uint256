import Extracted
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.DecMath
import Fv256.Arm64.DecT
import Fv256.Arm64.DecA

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI
open Fv256.E

namespace Fv256.Arm64.Dec

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- One iteration of the final-chunk loop (`lo ≥ 100`, head `fb+0x118`): two digits. -/
theorem fin_step (s : State) (ptr len lo i : Nat) (hlo : 100 ≤ lo) (hlo2 : lo < 2 ^ 29) (hi : 2 ≤ i) (hil : i ≤ len)
    (hp : ptr + len ≤ 2 ^ 48) (hacc : s.mem.accessible ptr len true = true) (hd : TabsOK s.mem)
    (hpc : s.pc = BitVec.ofNat 64 (fb + 0x118)) (e0 : s.regs 0 = BitVec.ofNat 64 ptr) (e2 : s.regs 2 = BitVec.ofNat 64 len)
    (e1 : s.regs 1 = BitVec.ofNat 64 i) (e3 : s.regs 3 = BitVec.ofNat 64 lo) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (fb + 0x118)) s (fun S' =>
      S'.regs 0 = BitVec.ofNat 64 ptr ∧ S'.regs 2 = BitVec.ofNat 64 len ∧ S'.regs 1 = BitVec.ofNat 64 (i - 2) ∧
      S'.regs 3 = BitVec.ofNat 64 (lo / 100) ∧
      (∀ k, k ∉ [1, 3, 4, 5, 6, 7, 8, 9, 10, 11] → S'.regs k = s.regs k) ∧ S'.sp = s.sp ∧
      S'.mem.readLE (ptr + i - 2) 1 = 48 + lo % 100 / 10 ∧ S'.mem.readLE (ptr + i - 1) 1 = 48 + lo % 10 ∧
      MemFrame s.mem S'.mem [(ptr + i - 2, ptr + i)] ∧ TabsOK S'.mem) := by
  have hc : fb + 0x300 < 2 ^ 47 := by decide
  tabs_data hd [hacc]
  have hx32 : lo < 2 ^ 32 := by omega
  have h1 := q1 lo hx32
  have h2 := q2 lo hx32
  have h3 := q3a lo hx32
  have h4 := q3 (lo % 100) (Nat.mod_lt _ (by omega))
  have h5 := q4 (lo % 100) (Nat.mod_lt _ (by omega))
  have hsw : (BitVec.setWidth 32 (BitVec.ofNat 64 lo)).toNat = lo := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : lo < 2 ^ 64), Nat.mod_eq_of_lt hx32]
  janus_run [hsw, e0, e1, e2, e3, h1, h2, h3, h4, h5] until [fb + 0x118]
  refine ReachesRet.done (by rfl) ?_
  have hsr := hd.sm (lo % 100) (Nat.mod_lt _ (by omega))
  have hm2 : 2 * (lo % 100) % 4294967296 = 2 * (lo % 100) := Nat.mod_eq_of_lt (by omega)
  simp only [hm2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setReg, e0]
  · simp [setReg, e2]
  · simp [setReg]; exact Fv256.E.ofNat_sub_ofNat i 2 (by omega) (by omega)
  · simp [setReg]
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setReg, hk]
  · trivial
  · rw [show ptr + i - 2 = ptr + (i - 2) by omega, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.pow_one]
    rw [hsr.1]; omega
  · rw [show ptr + i - 1 = ptr + (i - 1) by omega, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.pow_one]
    rw [show 1002589 + (2 * (lo % 100) + 1) = 1002589 + 2 * (lo % 100) + 1 by omega, hsr.2]; omega
  · exact ((MemFrame.refl s.mem [(ptr + i - 2, ptr + i)]).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
      (List.mem_singleton_self _) (by omega) (by omega)
  · exact hd.two hacc (by omega) (by omega) (by omega) (by omega) _ _
end Fv256.Arm64.Dec
