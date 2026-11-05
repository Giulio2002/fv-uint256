import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.UdivMathB
import Fv256.UdivremMath
import Fv256.KnuthMathB
import Fv256.Arm64.UdivremFront
import Fv256.Arm64.UdivremA

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.UdivremA Fv256.Arm64.UdivremFront

namespace Fv256.Arm64.UdivremC

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem caseL (T : State) (ret : W64) (Q : State → Prop) (M0 M : Memory) (R : Nat → W64) (fl : Flags)
    (qp up dp remp L x29 x30 : Nat)
    (hx30a : x30 % 4 = 0) (hx30b : x30 < 2 ^ 56)
    (hal : T.sp.toNat % 16 = 0) (hsp : 120 ≤ T.sp.toNat) (hspb : T.sp.toNat + 296 ≤ 2 ^ 48)
    (hL4 : 4 ≤ L) (hL : L ≤ 8) (hremp : remp < 2 ^ 64) (hup : up < 2 ^ 64)
    (hupb : up + 8 * L ≤ 2 ^ 48) (huacc : M.accessible up (8 * L) false = true)
    (hrem : remp ≠ 0 → remp + 32 ≤ 2 ^ 48 ∧ M.accessible remp 32 true = true ∧ (remp + 32 ≤ T.sp.toNat - 8 ∨ T.sp.toNat + 296 ≤ remp) ∧
      (remp + 32 ≤ up ∨ up + 8 * L ≤ remp))
    (hMc : M.accessible (T.sp.toNat - 8) 304 true = true)
    (r3 : R 3 = BitVec.ofNat 64 up) (r4 : R 4 = BitVec.ofNat 64 L) (r7 : R 7 = BitVec.ofNat 64 remp)
    (hs29 : M.readLE (T.sp.toNat - 8) 8 = x29) (hs30 : M.readLE T.sp.toNat 8 = x30)
    (hQ : ∀ (U : State) (R' : Nat → W64) (fl' : Flags) (Mf : Memory), U.sp = T.sp → R' 29 = BitVec.ofNat 64 x29 → R' 30 = BitVec.ofNat 64 x30 →
      (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 27, 29, 30] → R' i = R i) →
      (remp ≠ 0 → (∀ j, j < 4 → Mf.readLE (remp + 8 * j) 8 = M.readLE (up + 8 * j) 8) ∧ MemFrame M Mf [(remp, remp + 32)]) → (remp = 0 → Mf = M) →
      Q { U with regs := R', sp := U.sp + 224#64, pc := BitVec.ofNat 64 x30, flags := fl', mem := Mf }) :
    ReachesRet Extracted.program (BitVec.ofNat 64 x30) { T with regs := R, pc := BitVec.ofNat 64 ltpc, flags := fl, mem := M } Q := by
  have hcode := ku_lt
  janus_eval_nat hh1 : ltpc
  simp only [hh1]
  have hLt : ¬ ((BitVec.ofNat 64 L).toNat < 4) := by rw [BitVec.toNat_ofNat]; omega
  have hLi : ¬ ((BitVec.ofNat 64 L).toInt < 4) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]; omega
  have hLi' : ¬ ((L : Int) < 4) := by omega
  by_cases hr0 : remp = 0
  · subst hr0
    janus_run [r3, r4, r7, hs29, hs30, hLt, hLi, hLi']
    refine hQ T _ _ M rfl (by simp [setReg]) (by simp [setReg]) ?_ (fun h => absurd rfl h) (fun _ => rfl)
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    simp only [setReg]
    repeat' rw [if_neg (by omega)]
  · obtain ⟨hb, ha, hd, hdu⟩ := hrem hr0
    have hu32 : M.accessible up 32 false = true := Janus.Arm64.Memory.accessible_mono _ huacc (by omega) (by omega)
    janus_run [r3, r4, r7, hs29, hs30, hLt, hLi, hLi']
    have e1 : 32 + remp - 16 = remp + 16 := by omega
    have e2 : 32 + remp - 8 = remp + 24 := by omega
    have e3 : 32 + up - 16 = up + 16 := by omega
    have e4 : 32 + up - 8 = up + 24 := by omega
    have hlt : ∀ j, M.readLE (up + 8 * j) 8 < 2 ^ 64 := fun j => by
      have := Janus.Arm64.Memory.readLE_lt M (up + 8 * j) 8; simpa using this
    simp only [e1, e2, e3, e4]
    refine hQ T _ _ _ rfl (by simp [setReg]) (by simp [setReg]) ?_ (fun _ => ⟨?_, ?_⟩) (fun h => absurd h hr0)
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      simp only [setReg]
      repeat' rw [if_neg (by omega)]
    · intro j hj
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      have l0 : M.readLE up 8 < 2 ^ 64 := by simpa using hlt 0
      have l1 : M.readLE (up + 8) 8 < 2 ^ 64 := by simpa using hlt 1
      have l2 : M.readLE (up + 16) 8 < 2 ^ 64 := by simpa using hlt 2
      have l3 : M.readLE (up + 24) 8 < 2 ^ 64 := by simpa using hlt 3
      rcases this with rfl | rfl | rfl | rfl
      · simp (disch := omega) only [Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt l0
      · simp (disch := omega) only [Nat.reduceMul, Nat.reduceAdd, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt l1
      · simp (disch := omega) only [Nat.reduceMul, Nat.reduceAdd, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt l2
      · simp (disch := omega) only [Nat.reduceMul, Nat.reduceAdd, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt l3
    · have h0 := MemFrame.of_writeLE M (k := 8) (M.readLE up 8) (rs := [(remp, remp + 32)]) (a := remp) (r := (remp, remp + 32)) (by simp) (by simp <;> omega) (by simp <;> omega)
      have h1 := h0.writeLE (a := remp + 8) (k := 8) (M.readLE (up + 8) 8) (r := (remp, remp + 32)) (by simp) (by simp <;> omega) (by simp <;> omega)
      have h2 := h1.writeLE (a := remp + 16) (k := 8) (M.readLE (up + 16) 8) (r := (remp, remp + 32)) (by simp) (by simp <;> omega) (by simp <;> omega)
      exact h2.writeLE (a := remp + 24) (k := 8) (M.readLE (up + 24) 8) (r := (remp, remp + 32)) (by simp) (by simp <;> omega) (by simp <;> omega)

end Fv256.Arm64.UdivremC
