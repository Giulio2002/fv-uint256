import Fv256.Arm64.DecProg
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
/-- After the inner loop: the ninth digit of the chunk, then back to the head (`ud ≠ 0`, pc `fb+0x28`) or to the return block (`ud = 0`, `fb+0x1ec`). -/
theorem chunk_post (s : State) (tgt ptr len b lo ud : Nat)
    (htg : (ud ≠ 0 ∧ tgt = fb + 0x28) ∨ (ud = 0 ∧ tgt = fb + 0x1ec))
    (hb : 1 ≤ b) (hbl : b ≤ len) (hlo : lo < 10) (hud2 : ud < 2 ^ 64) (hp : ptr + len ≤ 2 ^ 48)
    (hacc : s.mem.accessible ptr len true = true) (hd : TabsOK s.mem)
    (hpc : s.pc = BitVec.ofNat 64 (fb + 0xd4)) (e0 : s.regs 0 = BitVec.ofNat 64 ptr) (e2 : s.regs 2 = BitVec.ofNat 64 len)
    (e1 : s.regs 1 = BitVec.ofNat 64 b) (e3 : s.regs 3 = BitVec.ofNat 64 lo) (e4 : s.regs 4 = BitVec.ofNat 64 ud) :
    ReachesRet Fv256.Arm64.DecProg.program (BitVec.ofNat 64 tgt) s (fun S' =>
      S'.regs 0 = BitVec.ofNat 64 ptr ∧ S'.regs 2 = BitVec.ofNat 64 len ∧ S'.regs 1 = BitVec.ofNat 64 (b - 1) ∧
      S'.regs 4 = BitVec.ofNat 64 ud ∧ (ud ≠ 0 → S'.regs 3 = BitVec.ofNat 64 ud) ∧ (∀ k, k ∉ [1, 3, 5, 6] → S'.regs k = s.regs k) ∧ S'.sp = s.sp ∧
      S'.mem.readLE (ptr + b - 1) 1 = 48 + lo ∧ MemFrame s.mem S'.mem [(ptr + b - 1, ptr + b)] ∧ TabsOK S'.mem) := by
  have hc : fb + 0x300 < 2 ^ 47 := by decide
  tabs_data hd [hacc]
  have hsr := hd.sm lo (by omega)
  have h5 := q5 lo (by omega)
  janus_run [e0, e1, e2, e3, e4, h5] until [fb + 0x28, fb + 0x1ec]
  all_goals (refine ReachesRet.done (by rcases htg with ⟨hj, rfl⟩ | ⟨rfl, rfl⟩ <;> first | rfl | (exfalso; omega) | (exfalso; simp at *; omega)) ?_)
  all_goals (
    have hm : 1002589 + (2 * lo + 1) = 1002589 + 2 * lo + 1 := by omega
    have hr1 : s.mem.readLE (1002589 + (2 * lo + 1)) 1 = 48 + lo := by rw [hm, hsr.2]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · simp [setReg, e0]
    · simp [setReg, e2]
    · simp [setReg]; exact Fv256.E.ofNat_sub_ofNat b 1 hb (by omega)
    · simp [setReg, e4]
    · intro hne; first | (exfalso; omega) | simp [setReg, e4]
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [setReg, hk]
    · rw [show ptr + b - 1 = ptr + (b - 1) by omega, Janus.Arm64.Memory.readLE_writeLE_self, hr1]
      simp only [Nat.pow_one]; omega
    · exact (MemFrame.refl s.mem _).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)
    · exact hd.writeLE (accessible_sub hacc (Or.inr rfl) (by omega) (by omega)) _)
end Fv256.Arm64.Dec
