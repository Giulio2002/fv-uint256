import Extracted
import Fv256.SpecE
import Fv256.UtilE
import Fv256.Amd64.DecA
import Fv256.Amd64.DecK

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E

namespace Fv256.Amd64.Dec

/-- The prologue of `formatBase10`: `PUSHQ BP; MOVQ SP, BP; MOVQ AX, 0x10(SP); MOVQ BX, CX; JMP`. -/
theorem entry_h1 (s : State) (hpc : s.rip = BitVec.ofNat 64 fb)
    (hsa : s.mem.accessible ((s.regs 4).toNat - 8) 24 true = true) (hsp : 8 ≤ (s.regs 4).toNat)
    (hspu : (s.regs 4).toNat + 16 ≤ 2 ^ 48) (hd : TabsOK s.mem) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (fb + 0x17)) s
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s with regs := R', rip := BitVec.ofNat 64 (fb + 0x17), flags := fl', mem := M' } ∧
        R' 0 = s.regs 0 ∧ R' 3 = s.regs 3 ∧ R' 1 = s.regs 3 ∧ R' 7 = s.regs 7 ∧
        R' 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 8) ∧ R' 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8) ∧
        (∀ k, k ∉ [1, 4, 5] → R' k = s.regs k) ∧
        M'.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧ M'.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 ∧
        MemFrame s.mem M' [((s.regs 4).toNat - 8, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] ∧
        TabsOK M') := by
  have hc : fb + 0x300 < 2 ^ 47 := by decide
  janus64_run
  have hs4 := (s.regs 4).isLt
  have hs5 := (s.regs 5).isLt
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setRegF]
  · simp [setRegF]
  · simp [setRegF]
  · simp [setRegF]
  · simp [setRegF]; exact bv_sub_lit _ 8 hsp
  · simp [setRegF]; exact bv_sub_lit _ 8 hsp
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setRegF, hk]
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simpa using hs5)
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  · exact ((MemFrame.refl s.mem _).writeLE _ (List.mem_cons_self ..) (by omega) (by omega)).writeLE _
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (by omega) (by omega)
  · exact TabsOK.writeLE (TabsOK.writeLE hd (accessible_sub hsa (Or.inr rfl) (by omega) (by omega)) _)
      (by simp only [Janus.Arm64.Memory.accessible_writeLE]; exact accessible_sub hsa (Or.inr rfl) (by omega) (by omega)) _
end Fv256.Amd64.Dec
