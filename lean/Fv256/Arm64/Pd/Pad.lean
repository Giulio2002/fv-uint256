import Fv256.Arm64.PrettyProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.PdCells
import Fv256.Arm64.P.T
import Fv256.Util
import Fv256.Arm64.Pd.Iter1
import Fv256.Arm64.Pd.Inner

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec
open Fv256.E Fv256.Arm64.P

namespace Fv256.Arm64.Pd

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- One pad iteration (`x3 = i < 19 - nn`): writes a separator when the comma counter is 3, otherwise only advances the cell counter. -/
theorem pd_pad_step (s : State) (b D nn i sepb z : Nat) (hpc : s.pc = BitVec.ofNat 64 pdK)
    (hi : nn + i < 19) (hnd1 : 1 ≤ nn) (hsb : sepb < 256) (hcb : cOf (D + 1) ≤ 132)
    (hb : 368 ≤ b) (hb2 : b + 424 ≤ 2 ^ 48)
    (hwa : s.mem.accessible (b + 99) 133 true = true)
    (e3 : s.regs 3 = BitVec.ofNat 64 i) (e1 : s.regs 1 = BitVec.ofNat 64 nn)
    (e4 : s.sp = BitVec.ofNat 64 b) (e9 : s.regs 9 = BitVec.ofNat 64 sepb)
    (e10 : s.regs 10 = BitVec.ofNat 64 (132 - cOf D)) (e11 : s.regs 11 = BitVec.ofNat 64 (cOf D % 4))
    (hcD : cOf D ≤ 132) (hzd : z / 10 ^ D % 10 = 0)
    (hout : OutIs s.mem (b + 231) sepb z (cOf D)) :
    ReachesRet Fv256.Arm64.PrettyProg.program (BitVec.ofNat 64 pdK) s
      (fun S' => S'.regs 3 = BitVec.ofNat 64 (i + 1) ∧
        S'.regs 10 = BitVec.ofNat 64 (132 - cOf (D + 1)) ∧ S'.regs 11 = BitVec.ofNat 64 (cOf (D + 1) % 4) ∧
        S'.sp = s.sp ∧ (∀ k, k ∉ [3, 8, 10, 11, 12] → S'.regs k = s.regs k) ∧
        MemFrame s.mem S'.mem [(b + 99, b + 232)] ∧ OutIs S'.mem (b + 231) sepb z (cOf (D + 1))) := by
  have hc1 : pdE + 0x5000 < 2 ^ 47 := by decide
  have htop : 132 ≤ b + 231 := by omega
  have hnd := cOf_succ D
  unfold nd at hnd
  have hz48 := pcell_cOf sepb z D
  rw [hzd] at hz48
  by_cases h3 : cOf D % 4 = 3
  · rw [if_pos h3] at hnd
    janus_run [e3, e1, e4, e9, e10, e11, h3] until [pdK]
    refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setReg]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · simp [setReg]
      rw [hnd, show 132 - (cOf D + 2) = (132 - cOf D) - 2 by omega]
      exact Fv256.E.ofNat_sub_ofNat (132 - cOf D) 2 (by omega) (by omega)
    · simp [setReg]
      rw [hnd, show (cOf D + 2) % 4 = 1 by omega]
    · simp [setReg]; exact e4.symm
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [setReg, hk]
    · exact ((MemFrame.refl _ _).writeLE _ (List.mem_singleton_self _) (by omega) (by omega))
    · dsimp only
      have o1 := OutIs.write hout htop (by omega) sepb (by rw [pcell_sep sepb z _ h3]; omega)
      rw [show b + 231 - cOf D = b + (99 + (132 - cOf D)) by omega] at o1
      have o2 := OutIs.pad o1 (by rw [hnd, show cOf D + 2 - 1 = cOf D + 1 by omega] at hz48; exact hz48)
      rw [hnd]
      exact o2
  · rw [if_neg h3] at hnd
    janus_run [e3, e1, e4, e9, e10, e11, h3] until [pdK]
    refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setReg]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
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
    · exact MemFrame.refl _ _
    · dsimp only
      have o2 := OutIs.pad hout (by rw [hnd, show cOf D + 1 - 1 = cOf D by omega] at hz48; exact hz48)
      rw [hnd]
      exact o2

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- The pad loop is done (`i = 19 - nn`): the continue block restores the loop-head registers. -/
theorem pd_pad_exit (s : State) (b nn i : Nat) (hpc : s.pc = BitVec.ofNat 64 pdK) (hnn : nn ≤ 19) (hi : nn + i = 19)
    (hb2 : b + 424 ≤ 2 ^ 48)
    (e3 : s.regs 3 = BitVec.ofNat 64 i) (e1 : s.regs 1 = BitVec.ofNat 64 nn) (e4 : s.sp = BitVec.ofNat 64 b) :
    ReachesRet Fv256.Arm64.PrettyProg.program (BitVec.ofNat 64 pdH) s
      (fun S' => S'.regs 0 = s.regs 2 ∧ S'.regs 2 = s.regs 10 ∧ S'.regs 8 = s.regs 0 ∧ S'.regs 4 = s.regs 11 ∧
        S'.regs 3 = BitVec.ofNat 64 (b + 320) ∧ S'.regs 6 = BitVec.ofNat 64 (b + 352) ∧ S'.sp = s.sp ∧
        (∀ k, k ∉ [0, 2, 3, 4, 6, 8, 12] → S'.regs k = s.regs k) ∧ S'.mem = s.mem) := by
  have hc1 : pdE + 0x5000 < 2 ^ 47 := by decide
  janus_run [e3, e1, e4] until [pdH]
  refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setReg]
  · simp [setReg]
  · simp [setReg]
  · simp [setReg]
  · simp [setReg]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · simp [setReg]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · simp [setReg]; exact e4.symm
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setReg, hk]
  · rfl

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- The pad loop: the `19 - nn` zero digits of a non-final chunk advance the cell counter (writing separators only). -/
theorem pd_pad_loop (b D0 nn sepb z : Nat) (hsb : sepb < 256) (hb : 368 ≤ b) (hb2 : b + 424 ≤ 2 ^ 48)
    (hnn : 1 ≤ nn) (hnn19 : nn ≤ 19) (hcb : cOf (D0 + 19) ≤ 132)
    (hpadz : ∀ i, D0 + nn ≤ i → i < D0 + 19 → z / 10 ^ i % 10 = 0) :
    ∀ p, p ≤ 19 - nn → ∀ s : State, s.pc = BitVec.ofNat 64 pdK →
      s.mem.accessible (b + 99) 133 true = true →
      s.regs 3 = BitVec.ofNat 64 (19 - nn - p) → s.regs 1 = BitVec.ofNat 64 nn → s.sp = BitVec.ofNat 64 b →
      s.regs 9 = BitVec.ofNat 64 sepb → s.regs 10 = BitVec.ofNat 64 (132 - cOf (D0 + 19 - p)) →
      s.regs 11 = BitVec.ofNat 64 (cOf (D0 + 19 - p) % 4) →
      OutIs s.mem (b + 231) sepb z (cOf (D0 + 19 - p)) →
      ReachesRet Fv256.Arm64.PrettyProg.program (BitVec.ofNat 64 pdH) s
        (fun S' => S'.regs 0 = s.regs 2 ∧ S'.regs 2 = BitVec.ofNat 64 (132 - cOf (D0 + 19)) ∧ S'.regs 8 = s.regs 0 ∧
          S'.regs 4 = BitVec.ofNat 64 (cOf (D0 + 19) % 4) ∧
          S'.regs 3 = BitVec.ofNat 64 (b + 320) ∧ S'.regs 6 = BitVec.ofNat 64 (b + 352) ∧ S'.sp = s.sp ∧
          (∀ k, k ∉ [0, 2, 3, 4, 6, 8, 10, 11, 12] → S'.regs k = s.regs k) ∧
          MemFrame s.mem S'.mem [(b + 99, b + 232)] ∧ OutIs S'.mem (b + 231) sepb z (cOf (D0 + 19))) := by
  intro p
  induction p with
  | zero =>
    intro hp s hpc hwa e3 e1 e4 e9 e10 e11 hout
    refine Fv256.E.reachesRet64_mono (pd_pad_exit s b nn (19 - nn - 0) hpc hnn19 (by omega) hb2 e3 e1 e4) ?_
    rintro S ⟨r0, r2, r8, r4, r3, r6, rsp, rk, rm⟩
    refine ⟨r0, ?_, r8, ?_, r3, r6, rsp, ?_, ?_, ?_⟩
    · rw [r2, e10]; simp
    · rw [r4, e11]; simp
    · intro k hk; exact rk k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega)
    · rw [rm]; exact MemFrame.refl _ _
    · rw [rm]; simpa using hout
  | succ p ih =>
    intro hp s hpc hwa e3 e1 e4 e9 e10 e11 hout
    have hD : D0 + 19 - (p + 1) + 1 = D0 + 19 - p := by omega
    have hcbD : cOf (D0 + 19 - (p + 1) + 1) ≤ 132 := by
      have := cOf_mono (D0 + 19 - (p + 1) + 1) (D0 + 19) (by omega)
      omega
    have hcD : cOf (D0 + 19 - (p + 1)) ≤ 132 := by
      have := cOf_mono (D0 + 19 - (p + 1)) (D0 + 19) (by omega)
      omega
    have hzd := hpadz (D0 + 19 - (p + 1)) (by omega) (by omega)
    refine Fv256.E.reachesRet64_bind (pd_pad_step s b (D0 + 19 - (p + 1)) nn (19 - nn - (p + 1)) sepb z hpc (by omega) hnn hsb hcbD hb hb2
      hwa e3 e1 e4 e9 e10 e11 hcD hzd hout) ?_
    intro S hrip ⟨r3, r10, r11, rsp, rk, hfr, hoS⟩
    rw [hD] at r10 r11 hoS
    refine Fv256.E.reachesRet64_mono (ih (by omega) S hrip ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · rw [hfr.accessible]; exact hwa
    · rw [r3]; congr 1; omega
    · rw [rk 1 (by simp)]; exact e1
    · rw [rsp]; exact e4
    · rw [rk 9 (by simp)]; exact e9
    · rw [r10]
    · rw [r11]
    · exact hoS
    · rintro S2 ⟨q0, q2, q8, q4, q3, q6, qsp, qk, qm, qo⟩
      refine ⟨?_, q2, ?_, q4, q3, q6, ?_, ?_, ?_, qo⟩
      · rw [q0, rk 2 (by simp)]
      · rw [q8, rk 0 (by simp)]
      · rw [qsp, rsp]
      · intro k hk
        rw [qk k hk, rk k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega)]
      · exact hfr.trans qm (fun a n h => ⟨h, h⟩)
end Fv256.Arm64.Pd
