import Fv256.Proofs.Arm64.DecProg
import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.UtilE
import Fv256.Proofs.Common.UtilE64
import Fv256.Proofs.Common.DecMath
import Fv256.Proofs.Arm64.DecT
import Fv256.Proofs.Arm64.DecA

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec
open Fv256.E

namespace Fv256.Arm64.Dec

set_option maxHeartbeats 8000000 in
/-- The prologue of `formatBase10`, up to the loop head `fb+0x28`. -/
theorem entry_h1 (s : State) (hpc : s.pc = BitVec.ofNat 64 fb) (hg : GuardOK s 0)
    (hal : s.sp.toNat % 16 = 0) (hb : 24 ≤ s.sp.toNat) (ha : s.sp.toNat + 16 ≤ 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 24) 40 true = true) :
    ReachesRet Fv256.Arm64.DecProg.program (BitVec.ofNat 64 (fb + 0x28)) s (fun S' =>
      S'.regs 0 = s.regs 0 ∧ S'.regs 1 = s.regs 1 ∧ S'.regs 2 = s.regs 1 ∧ S'.regs 3 = s.regs 3 ∧
      S'.sp = s.sp - 16#64 ∧ S'.regs 29 = s.sp - 24#64 ∧ (∀ k, k ∉ [2, 29, 16] → S'.regs k = s.regs k) ∧
      S'.mem.readLE (s.sp.toNat - 24) 8 = (s.regs 29).toNat ∧ S'.mem.readLE (s.sp.toNat - 16) 8 = (s.regs 30).toNat ∧
      S'.mem.readLE (s.sp.toNat + 8) 8 = (s.regs 0).toNat ∧
      MemFrame s.mem S'.mem [(s.sp.toNat - 24, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 16)]) := by
  have hc : fb + 0x300 < 2 ^ 47 := by decide
  obtain ⟨hg1, hg2, hg3⟩ := hg
  janus_run until [fb + 0x28]
  refine ReachesRet.done (by rfl) ?_
  have hs := s.sp.isLt
  have hr0 := (s.regs 0).isLt
  have hr29 := (s.regs 29).isLt
  have hr30 := (s.regs 30).isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setReg]
  · simp [setReg]
  · simp [setReg]
  · simp [setReg]
  · rfl
  · simp [setReg]
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setReg, hk]
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
      Nat.mod_eq_of_lt (by simpa using hr29)]
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by simpa using hr30)]
  · rw [Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by simpa using hr0)]
  · exact (((MemFrame.refl s.mem _).writeLE _ (List.mem_cons_self ..) (by omega) (by omega)).writeLE _
      (List.mem_cons_self ..) (by omega) (by omega)).writeLE _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (by omega) (by omega)

set_option maxHeartbeats 8000000 in
/-- Loop head with `u < 2^29`: straight to the final chunk (`fb+0x118`). -/
theorem to_final (s : State) (u : Nat) (hu : u < 2 ^ 29) (hpc : s.pc = BitVec.ofNat 64 (fb + 0x28))
    (e3 : s.regs 3 = BitVec.ofNat 64 u) :
    ReachesRet Fv256.Arm64.DecProg.program (BitVec.ofNat 64 (fb + 0x118)) s (fun S' =>
      S'.regs 3 = BitVec.ofNat 64 u ∧ (∀ k, k ∉ [4] → S'.regs k = s.regs k) ∧ S'.sp = s.sp ∧ S'.mem = s.mem) := by
  have hc : fb + 0x300 < 2 ^ 47 := by decide
  have h29 : (((BitVec.ofNat 64 u).rotateRight 29).toNat % 34359738368 = 0) = True := by
    apply eq_true
    have := rot_lsr u 29 (by omega) (by omega) (by omega)
    simp only [show 64 - 29 = 35 from rfl, show (2:Nat)^35 = 34359738368 from rfl] at this
    rw [this]
    exact Nat.div_eq_of_lt (by omega)
  janus_run [e3, h29] until [fb + 0x118]
  refine ReachesRet.done (by rfl) ⟨?_, ?_, rfl, rfl⟩
  · simp [setReg, e3]
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    simp [setReg, hk]
end Fv256.Arm64.Dec
