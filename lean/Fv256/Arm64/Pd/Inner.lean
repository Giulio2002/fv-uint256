import Fv256.Arm64.PrettyProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.PdCells
import Fv256.Arm64.P.T
import Fv256.Util
import Fv256.Arm64.Pd.Iter1

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec
open Fv256.E Fv256.Arm64.P

namespace Fv256.Arm64.Pd

theorem msb19 : ∀ m, m < 20 → (BitVec.ofNat 64 m).getLsbD 63 = false := by decide

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem pd_inner_step (s : State) (b D m sepb z : Nat) (hpc : s.pc = BitVec.ofNat 64 pdI)
    (hm : 1 ≤ m) (hm19 : m ≤ 19) (hsb : sepb < 256) (hcb : cOf (D + 1) ≤ 132)
    (hb : 368 ≤ b) (hb2 : b + 424 ≤ 2 ^ 48)
    (hwa : s.mem.accessible (b + 99) 133 true = true) (hbw : s.mem.accessible (b + 80) 19 true = true)
    (e0 : s.regs 0 = BitVec.ofNat 64 (b + 0x50)) (e2 : s.regs 8 = BitVec.ofNat 64 (m - 1))
    (e4 : s.sp = BitVec.ofNat 64 b) (e11 : s.regs 9 = BitVec.ofNat 64 sepb)
    (e12 : s.regs 10 = BitVec.ofNat 64 (132 - cOf D)) (e13 : s.regs 11 = BitVec.ofNat 64 (cOf D % 4))
    (hcD : cOf D ≤ 132)
    (hdig : s.mem.readLE (b + 0x50 + (m - 1)) 1 = 48 + z / 10 ^ D % 10)
    (hout : OutIs s.mem (b + 231) sepb z (cOf D)) :
    ReachesRet Fv256.Arm64.PrettyProg.program (BitVec.ofNat 64 pdI) s
      (fun S' => S'.regs 0 = s.regs 0 ∧ S'.regs 8 = BitVec.ofNat 64 (m - 1) - 1#64 ∧ S'.regs 9 = s.regs 9 ∧
        S'.regs 10 = BitVec.ofNat 64 (132 - cOf (D + 1)) ∧ S'.regs 11 = BitVec.ofNat 64 (cOf (D + 1) % 4) ∧
        S'.sp = s.sp ∧ (∀ k, k ∉ [8, 10, 11, 12, 13] → S'.regs k = s.regs k) ∧
        MemFrame s.mem S'.mem [(b + 99, b + 232)] ∧ OutIs S'.mem (b + 231) sepb z (cOf (D + 1))) := by
  have hc1 : pdE + 0x5000 < 2 ^ 47 := by decide
  have hmsb : (BitVec.ofNat 64 (m - 1)).getLsbD 63 = false := msb19 _ (by omega)
  have hsub1 : BitVec.ofNat 64 (m - 1) - 1#64 = BitVec.ofNat 64 (m - 1) - BitVec.ofNat 64 1 := rfl
  have htop : 132 ≤ b + 231 := by omega
  have hsb' : sepb % 256 % 256 = sepb := by omega
  have hnd := cOf_succ D
  unfold nd at hnd
  by_cases h3 : cOf D % 4 = 3
  · rw [if_pos h3] at hnd
    janus_run [e0, e2, e4, e11, e12, e13, h3, hmsb] until [pdI]
    refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
      rw [hnd, show 132 - (cOf D + 2) = (132 - cOf D) - 2 by omega]
      exact Fv256.E.ofNat_sub_ofNat (132 - cOf D) 2 (by omega) (by omega)
    · simp [setReg]
      rw [hnd, show (cOf D + 2) % 4 = 1 by omega]
    · simp [setReg]; exact e4.symm
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [setReg, hk]
    · exact ((MemFrame.refl _ _).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
        (List.mem_singleton_self _) (by omega) (by omega)
    · dsimp only
      have o1 := OutIs.write hout htop (by omega) sepb (by rw [pcell_sep sepb z _ h3]; omega)
      rw [show b + 231 - cOf D = b + (99 + (132 - cOf D)) by omega] at o1
      have o2 := OutIs.write o1 htop (by omega) (s.mem.readLE (b + 80 + (m - 1)) 1) (by
        have := pcell_cOf sepb z D
        rw [hnd, show cOf D + 2 - 1 = cOf D + 1 by omega] at this
        rw [this, hdig]; omega)
      rw [show b + 231 - (cOf D + 1) = b + 99 + (132 - cOf D - 1) by omega] at o2
      rw [hnd]
      exact o2
  · rw [if_neg h3] at hnd
    janus_run [e0, e2, e4, e11, e12, e13, h3, hmsb] until [pdI]
    refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
      rw [hnd]
      exact Fv256.E.ofNat_sub_ofNat (132 - cOf D) 1 (by omega) (by omega)
    · simp [setReg]
      rw [hnd]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · simp [setReg]; exact e4.symm
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [setReg, hk]
    · exact ((MemFrame.refl _ _).writeLE _ (List.mem_singleton_self _) (by omega) (by omega))
    · dsimp only
      have o2 := OutIs.write hout htop (by omega) (s.mem.readLE (b + 80 + (m - 1)) 1) (by
        have := pcell_cOf sepb z D
        rw [hnd, show cOf D + 1 - 1 = cOf D by omega] at this
        rw [this, hdig]; omega)
      rw [show b + 231 - cOf D = b + (99 + (132 - cOf D)) by omega] at o2
      rw [hnd]
      exact o2

set_option maxHeartbeats 8000000 in
/-- The exit of the inner loop: `rdx = -1`, jump to `pdJ`. -/
theorem pd_inner_exit (s : State) (hpc : s.pc = BitVec.ofNat 64 pdI) (e2 : s.regs 8 = 18446744073709551615#64) :
    ReachesRet Fv256.Arm64.PrettyProg.program (BitVec.ofNat 64 pdJ) s
      (fun S' => S'.regs = s.regs ∧ S'.mem = s.mem ∧ S'.sp = s.sp) := by
  have hc1 : pdE + 0x5000 < 2 ^ 47 := by decide
  have hmsb : (18446744073709551615#64).getLsbD 63 = true := by decide
  janus_run [e2, hmsb] until [pdJ]
  exact ReachesRet.done (by rfl) ⟨rfl, rfl, rfl⟩

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- The inner copy loop: writes the `nd` digits held in `buf` (least significant at the end), with the separators, into `out`. -/
theorem pd_inner_loop (b D0 nd sepb z : Nat) (hsb : sepb < 256) (hb : 368 ≤ b) (hb2 : b + 424 ≤ 2 ^ 48)
    (hnd : nd ≤ 19) (hcb : cOf (D0 + nd) ≤ 132) :
    ∀ m, m ≤ nd → ∀ s : State, s.pc = BitVec.ofNat 64 pdI →
      s.mem.accessible (b + 99) 133 true = true → s.mem.accessible (b + 80) 19 true = true →
      s.regs 0 = BitVec.ofNat 64 (b + 0x50) → s.regs 8 = BitVec.ofNat 64 m - 1#64 → s.sp = BitVec.ofNat 64 b →
      s.regs 9 = BitVec.ofNat 64 sepb → s.regs 10 = BitVec.ofNat 64 (132 - cOf (D0 + nd - m)) →
      s.regs 11 = BitVec.ofNat 64 (cOf (D0 + nd - m) % 4) →
      (∀ j, j < m → s.mem.readLE (b + 80 + j) 1 = 48 + z / 10 ^ (D0 + nd - 1 - j) % 10) →
      OutIs s.mem (b + 231) sepb z (cOf (D0 + nd - m)) →
      ReachesRet Fv256.Arm64.PrettyProg.program (BitVec.ofNat 64 pdJ) s
        (fun S' => (∀ k, k ∉ [8, 10, 11, 12, 13] → S'.regs k = s.regs k) ∧
          S'.regs 10 = BitVec.ofNat 64 (132 - cOf (D0 + nd)) ∧ S'.regs 11 = BitVec.ofNat 64 (cOf (D0 + nd) % 4) ∧
          S'.sp = s.sp ∧ MemFrame s.mem S'.mem [(b + 99, b + 232)] ∧
          OutIs S'.mem (b + 231) sepb z (cOf (D0 + nd))) := by
  intro m
  induction m with
  | zero =>
    intro hm s hpc hwa hbw e0 e2 e4 e11 e12 e13 hdig hout
    refine Fv256.E.reachesRet64_mono (pd_inner_exit s hpc (by rw [e2]; decide)) ?_
    rintro S ⟨hr, hm', hx⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk; rw [hr]
    · rw [hr, e12]; simp
    · rw [hr, e13]; simp
    · exact hx
    · rw [hm']; exact MemFrame.refl _ _
    · rw [hm']; simpa using hout
  | succ m ih =>
    intro hm s hpc hwa hbw e0 e2 e4 e11 e12 e13 hdig hout
    have hD : D0 + nd - (m + 1) + 1 = D0 + nd - m := by omega
    have e2' : s.regs 8 = BitVec.ofNat 64 (m + 1 - 1) := by
      rw [e2]; exact Fv256.E.ofNat_sub_ofNat (m + 1) 1 (by omega) (by omega)
    have hcbD : cOf (D0 + nd - (m + 1) + 1) ≤ 132 := by
      have := cOf_mono (D0 + nd - (m + 1) + 1) (D0 + nd) (by omega)
      omega
    have hcD : cOf (D0 + nd - (m + 1)) ≤ 132 := by
      have := cOf_mono (D0 + nd - (m + 1)) (D0 + nd) (by omega)
      omega
    have hd1 := hdig m (by omega)
    rw [show D0 + nd - 1 - m = D0 + nd - (m + 1) by omega] at hd1
    refine Fv256.E.reachesRet64_bind (pd_inner_step s b (D0 + nd - (m + 1)) (m + 1) sepb z hpc (by omega) (by omega) hsb hcbD hb hb2
      hwa hbw e0 e2' e4 e11 e12 e13 hcD (by rw [show m + 1 - 1 = m by omega]; exact hd1) hout) ?_
    intro S hrip ⟨r0, r2, r11, r12, r13, rsp, rk, hfr, hoS⟩
    rw [hD] at r12 r13 hoS
    have hfr1 := hfr
    refine Fv256.E.reachesRet64_mono (ih (by omega) S hrip ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · rw [hfr.accessible]; exact hwa
    · rw [hfr.accessible]; exact hbw
    · rw [r0]; exact e0
    · rw [r2]; rw [show m + 1 - 1 = m by omega]
    · rw [rsp]; exact e4
    · rw [r11]; exact e11
    · rw [r12]
    · rw [r13]
    · intro j hj
      rw [hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      exact hdig j (by omega)
    · exact hoS
    · rintro S2 ⟨q1, q2, q3, q4, q6, q7⟩
      refine ⟨?_, q2, q3, ?_, ?_, q7⟩
      · intro k hk; rw [q1 k hk, rk k hk]
      · rw [q4]; exact rsp
      · exact hfr.trans q6 (fun a n h => ⟨h, h⟩)
end Fv256.Arm64.Pd
