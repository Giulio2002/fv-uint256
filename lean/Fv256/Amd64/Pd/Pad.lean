import Fv256.PrettyProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.PdCells
import Fv256.Amd64.P.T
import Fv256.Util
import Fv256.Amd64.Pd.Iter1

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E Fv256.Amd64.P

namespace Fv256.Amd64.Pd

/-- the pad loop head (`LEAQ -0x13(BX), R15`) -/
def pdK : Nat := pdE + 0x2a8

theorem neg19 : ∀ nn, nn ≤ 19 → (0#64 - (BitVec.ofNat 64 nn - 19#64)).toInt = ((19 - nn : Nat) : Int) := by decide

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem pd_pad_step (s : State) (b D nn i sepb z : Nat) (hpc : s.rip = BitVec.ofNat 64 pdK)
    (hi : nn + i < 19) (hnd1 : 1 ≤ nn) (hsb : sepb < 256) (hcb : cOf (D + 1) ≤ 132)
    (hb : 0x180 ≤ b) (hb2 : b + 0x198 ≤ 2 ^ 48)
    (hwa : s.mem.accessible (b + 83) 133 true = true)
    (e2 : s.regs 2 = BitVec.ofNat 64 i) (e3 : s.regs 3 = BitVec.ofNat 64 nn)
    (e4 : s.regs 4 = BitVec.ofNat 64 b) (e11 : s.regs 11 = BitVec.ofNat 64 sepb)
    (e12 : s.regs 12 = BitVec.ofNat 64 (132 - cOf D)) (e13 : s.regs 13 = BitVec.ofNat 64 (cOf D % 4))
    (hcD : cOf D ≤ 132) (hzd : z / 10 ^ D % 10 = 0)
    (hout : OutIs s.mem (b + 215) sepb z (cOf D)) :
    ReachesRet Fv256.PrettyProg.program (BitVec.ofNat 64 pdK) s
      (fun S' => S'.regs 2 = BitVec.ofNat 64 (i + 1) ∧
        S'.regs 12 = BitVec.ofNat 64 (132 - cOf (D + 1)) ∧ S'.regs 13 = BitVec.ofNat 64 (cOf (D + 1) % 4) ∧
        (∀ k, k ∉ [2, 12, 13, 15] → S'.regs k = s.regs k) ∧ S'.xmm = s.xmm ∧ S'.df = s.df ∧
        MemFrame s.mem S'.mem [(b + 83, b + 216)] ∧ OutIs S'.mem (b + 215) sepb z (cOf (D + 1))) := by
  have hc1 : pdE + 0x5000 < 2 ^ 47 := by decide
  have hr15 := neg19 nn (by omega)
  have htop : 132 ≤ b + 215 := by omega
  have hsb' : sepb % 256 % 256 = sepb := by omega
  have hnd := cOf_succ D
  unfold nd at hnd
  have hz48 := pcell_cOf sepb z D
  rw [hzd] at hz48
  by_cases h3 : cOf D % 4 = 3
  · rw [if_pos h3] at hnd
    janus64_run [e2, e3, e4, e11, e12, e13, h3] until [pdK]
    refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF]
    · simp [setRegF]
      rw [hnd, show 132 - (cOf D + 2) = (132 - cOf D) - 2 by omega]
      exact Fv256.E.ofNat_sub_ofNat (132 - cOf D) 2 (by omega) (by omega)
    · simp [setRegF]
      rw [hnd, show (cOf D + 2) % 4 = 1 by omega]
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [setRegF, hk]
    · rfl
    · rfl
    · exact ((MemFrame.refl _ _).writeLE _ (List.mem_singleton_self _) (by omega) (by omega))
    · dsimp only
      have o1 := OutIs.write hout htop (by omega) (sepb % 256) (by rw [pcell_sep sepb z _ h3]; exact hsb')
      rw [show b + 215 - cOf D = b + (132 - cOf D + 83) by omega] at o1
      have o2 := OutIs.pad o1 (by rw [hnd, show cOf D + 2 - 1 = cOf D + 1 by omega] at hz48; exact hz48)
      rw [hnd]
      exact o2
  · rw [if_neg h3] at hnd
    janus64_run [e2, e3, e4, e11, e12, e13, h3] until [pdK]
    refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF]
    · simp [setRegF]
      rw [hnd]
      exact Fv256.E.ofNat_sub_ofNat (132 - cOf D) 1 (by omega) (by omega)
    · simp [setRegF]
      rw [hnd]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [setRegF, hk]
    · rfl
    · rfl
    · exact MemFrame.refl _ _
    · dsimp only
      have o2 := OutIs.pad hout (by rw [hnd, show cOf D + 1 - 1 = cOf D by omega] at hz48; exact hz48)
      rw [hnd]
      exact o2

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- The pad loop is done (`i = 19 - nn`): the continue block restores the loop-head registers. -/
theorem pd_pad_exit (s : State) (b nn i : Nat) (hpc : s.rip = BitVec.ofNat 64 pdK) (hnn : nn ≤ 19) (hi : nn + i = 19)
    (e2 : s.regs 2 = BitVec.ofNat 64 i) (e3 : s.regs 3 = BitVec.ofNat 64 nn) (e4 : s.regs 4 = BitVec.ofNat 64 b) :
    ReachesRet Fv256.PrettyProg.program (BitVec.ofNat 64 pdH) s
      (fun S' => S'.regs 0 = s.regs 1 ∧ S'.regs 1 = s.regs 12 ∧ S'.regs 2 = s.regs 0 ∧ S'.regs 6 = s.regs 13 ∧
        S'.regs 7 = BitVec.ofNat 64 (b + 0x130) ∧ S'.regs 9 = BitVec.ofNat 64 (b + 0x150) ∧
        (∀ k, k ∉ [0, 1, 2, 6, 7, 9, 15] → S'.regs k = s.regs k) ∧ S'.mem = s.mem ∧ S'.xmm = s.xmm ∧ S'.df = s.df) := by
  have hc1 : pdE + 0x5000 < 2 ^ 47 := by decide
  have hr15 := neg19 nn hnn
  janus64_run [e2, e3, e4] until [pdH]
  refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setRegF]
  · simp [setRegF]
  · simp [setRegF]
  · simp [setRegF]
  · simp [setRegF]
    rw [← BitVec.ofNat_add]
  · simp [setRegF]
    rw [← BitVec.ofNat_add]
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setRegF, hk]
  · rfl
  · rfl
  · rfl

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- The pad loop: the `19 - nn` zero digits of a non-final chunk advance the cell counter (writing separators only). -/
theorem pd_pad_loop (b D0 nn sepb z : Nat) (hsb : sepb < 256) (hb : 0x180 ≤ b) (hb2 : b + 0x198 ≤ 2 ^ 48)
    (hnn : 1 ≤ nn) (hnn19 : nn ≤ 19) (hcb : cOf (D0 + 19) ≤ 132)
    (hpadz : ∀ i, D0 + nn ≤ i → i < D0 + 19 → z / 10 ^ i % 10 = 0) :
    ∀ p, p ≤ 19 - nn → ∀ s : State, s.rip = BitVec.ofNat 64 pdK →
      s.mem.accessible (b + 83) 133 true = true →
      s.regs 2 = BitVec.ofNat 64 (19 - nn - p) → s.regs 3 = BitVec.ofNat 64 nn → s.regs 4 = BitVec.ofNat 64 b →
      s.regs 11 = BitVec.ofNat 64 sepb → s.regs 12 = BitVec.ofNat 64 (132 - cOf (D0 + 19 - p)) →
      s.regs 13 = BitVec.ofNat 64 (cOf (D0 + 19 - p) % 4) →
      OutIs s.mem (b + 215) sepb z (cOf (D0 + 19 - p)) →
      ReachesRet Fv256.PrettyProg.program (BitVec.ofNat 64 pdH) s
        (fun S' => S'.regs 0 = s.regs 1 ∧ S'.regs 1 = BitVec.ofNat 64 (132 - cOf (D0 + 19)) ∧ S'.regs 2 = s.regs 0 ∧
          S'.regs 6 = BitVec.ofNat 64 (cOf (D0 + 19) % 4) ∧
          S'.regs 7 = BitVec.ofNat 64 (b + 0x130) ∧ S'.regs 9 = BitVec.ofNat 64 (b + 0x150) ∧
          (∀ k, k ∉ [0, 1, 2, 6, 7, 9, 12, 13, 15] → S'.regs k = s.regs k) ∧ S'.xmm = s.xmm ∧ S'.df = s.df ∧
          MemFrame s.mem S'.mem [(b + 83, b + 216)] ∧ OutIs S'.mem (b + 215) sepb z (cOf (D0 + 19))) := by
  intro p
  induction p with
  | zero =>
    intro hp s hpc hwa e2 e3 e4 e11 e12 e13 hout
    refine ReachesRet.mono (pd_pad_exit s b nn (19 - nn - 0) hpc hnn19 (by omega) e2 e3 e4) ?_
    rintro S ⟨r0, r1, r2, r6, r7, r9, rk, rm, rx, rdf⟩
    refine ⟨r0, ?_, r2, ?_, r7, r9, ?_, rx, rdf, ?_, ?_⟩
    · rw [r1, e12]; simp
    · rw [r6, e13]; simp
    · intro k hk; exact rk k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega)
    · rw [rm]; exact MemFrame.refl _ _
    · rw [rm]; simpa using hout
  | succ p ih =>
    intro hp s hpc hwa e2 e3 e4 e11 e12 e13 hout
    have hD : D0 + 19 - (p + 1) + 1 = D0 + 19 - p := by omega
    have hcbD : cOf (D0 + 19 - (p + 1) + 1) ≤ 132 := by
      have := cOf_mono (D0 + 19 - (p + 1) + 1) (D0 + 19) (by omega)
      omega
    have hcD : cOf (D0 + 19 - (p + 1)) ≤ 132 := by
      have := cOf_mono (D0 + 19 - (p + 1)) (D0 + 19) (by omega)
      omega
    have hzd := hpadz (D0 + 19 - (p + 1)) (by omega) (by omega)
    refine Fv256.E.reachesRet_bind' (pd_pad_step s b (D0 + 19 - (p + 1)) nn (19 - nn - (p + 1)) sepb z hpc (by omega) hnn hsb hcbD hb hb2
      hwa e2 e3 e4 e11 e12 e13 hcD hzd hout) ?_
    intro S hrip ⟨r2, r12, r13, rk, rx, rdf, hfr, hoS⟩
    rw [hD] at r12 r13 hoS
    refine ReachesRet.mono (ih (by omega) S hrip ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · rw [hfr.accessible]; exact hwa
    · rw [r2]; congr 1; omega
    · rw [rk 3 (by simp)]; exact e3
    · rw [rk 4 (by simp)]; exact e4
    · rw [rk 11 (by simp)]; exact e11
    · rw [r12]
    · rw [r13]
    · exact hoS
    · rintro S2 ⟨q0, q1, q2, q6, q7, q9, qk, qx, qdf, qm, qo⟩
      refine ⟨?_, q1, ?_, q6, q7, q9, ?_, ?_, ?_, ?_, qo⟩
      · rw [q0, rk 1 (by simp)]
      · rw [q2, rk 0 (by simp)]
      · intro k hk
        rw [qk k hk, rk k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega)]
      · rw [qx]; exact rx
      · rw [qdf]; exact rdf
      · exact hfr.trans qm (fun a n h => ⟨h, h⟩)
end Fv256.Amd64.Pd
