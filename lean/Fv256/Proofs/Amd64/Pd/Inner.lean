import Fv256.Proofs.Common.PrettyProg
import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.UtilE
import Fv256.Proofs.Common.PdCells
import Fv256.Proofs.Amd64.P.T
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Amd64.Pd.Iter1

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E Fv256.Amd64.P

namespace Fv256.Amd64.Pd

theorem msb19 : ∀ m, m < 20 → (BitVec.ofNat 64 m).msb = false := by decide

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem pd_inner_step (s : State) (b D m sepb z : Nat) (hpc : s.rip = BitVec.ofNat 64 pdI)
    (hm : 1 ≤ m) (hm19 : m ≤ 19) (hsb : sepb < 256) (hcb : cOf (D + 1) ≤ 132)
    (hb : 0x180 ≤ b) (hb2 : b + 0x198 ≤ 2 ^ 48)
    (hwa : s.mem.accessible (b + 83) 133 true = true) (hbw : s.mem.accessible (b + 64) 19 true = true)
    (e0 : s.regs 0 = BitVec.ofNat 64 (b + 0x40)) (e2 : s.regs 2 = BitVec.ofNat 64 (m - 1))
    (e4 : s.regs 4 = BitVec.ofNat 64 b) (e11 : s.regs 11 = BitVec.ofNat 64 sepb)
    (e12 : s.regs 12 = BitVec.ofNat 64 (132 - cOf D)) (e13 : s.regs 13 = BitVec.ofNat 64 (cOf D % 4))
    (hcD : cOf D ≤ 132)
    (hdig : s.mem.readLE (b + 0x40 + (m - 1)) 1 = 48 + z / 10 ^ D % 10)
    (hout : OutIs s.mem (b + 215) sepb z (cOf D)) :
    ReachesRet Fv256.PrettyProg.program (BitVec.ofNat 64 pdI) s
      (fun S' => S'.regs 0 = s.regs 0 ∧ S'.regs 2 = BitVec.ofNat 64 (m - 1) - 1#64 ∧ S'.regs 11 = s.regs 11 ∧
        S'.regs 12 = BitVec.ofNat 64 (132 - cOf (D + 1)) ∧ S'.regs 13 = BitVec.ofNat 64 (cOf (D + 1) % 4) ∧
        (∀ k, k ∉ [2, 12, 13, 15] → S'.regs k = s.regs k) ∧ S'.xmm = s.xmm ∧ S'.df = s.df ∧
        MemFrame s.mem S'.mem [(b + 83, b + 216)] ∧ OutIs S'.mem (b + 215) sepb z (cOf (D + 1))) := by
  have hc1 : pdE + 0x5000 < 2 ^ 47 := by decide
  have hmsb : (BitVec.ofNat 64 (m - 1)).msb = false := msb19 _ (by omega)
  have hsub1 : BitVec.ofNat 64 (m - 1) - 1#64 = BitVec.ofNat 64 (m - 1) - BitVec.ofNat 64 1 := rfl
  have htop : 132 ≤ b + 215 := by omega
  have hsb' : sepb % 256 % 256 = sepb := by omega
  have hnd := cOf_succ D
  unfold nd at hnd
  by_cases h3 : cOf D % 4 = 3
  · rw [if_pos h3] at hnd
    janus64_run [e0, e2, e4, e11, e12, e13, h3, hmsb] until [pdI]
    refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF]
    · simp [setRegF]
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
    · exact ((MemFrame.refl _ _).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
        (List.mem_singleton_self _) (by omega) (by omega)
    · dsimp only
      have o1 := OutIs.write hout htop (by omega) (sepb % 256) (by rw [pcell_sep sepb z _ h3]; exact hsb')
      rw [show b + 215 - cOf D = b + (132 - cOf D + 83) by omega] at o1
      have o2 := OutIs.write o1 htop (by omega) ((48 + z / 10 ^ D % 10) % 256) (by
        have := pcell_cOf sepb z D
        rw [hnd, show cOf D + 2 - 1 = cOf D + 1 by omega] at this
        rw [this]; omega)
      rw [show b + 215 - (cOf D + 1) = b + (132 - cOf D - 1) + 83 by omega] at o2
      rw [hnd]
      exact o2
  · rw [if_neg h3] at hnd
    janus64_run [e0, e2, e4, e11, e12, e13, h3, hmsb] until [pdI]
    refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF]
    · simp [setRegF]
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
    · exact ((MemFrame.refl _ _).writeLE _ (List.mem_singleton_self _) (by omega) (by omega))
    · dsimp only
      have o2 := OutIs.write hout htop (by omega) ((48 + z / 10 ^ D % 10) % 256) (by
        have := pcell_cOf sepb z D
        rw [hnd, show cOf D + 1 - 1 = cOf D by omega] at this
        rw [this]; omega)
      rw [show b + 215 - cOf D = b + (132 - cOf D) + 83 by omega] at o2
      rw [hnd]
      exact o2

set_option maxHeartbeats 8000000 in
/-- The exit of the inner loop: `rdx = -1`, jump to `pdJ`. -/
theorem pd_inner_exit (s : State) (hpc : s.rip = BitVec.ofNat 64 pdI) (e2 : s.regs 2 = 18446744073709551615#64) :
    ReachesRet Fv256.PrettyProg.program (BitVec.ofNat 64 pdJ) s
      (fun S' => S'.regs = s.regs ∧ S'.mem = s.mem ∧ S'.xmm = s.xmm ∧ S'.df = s.df) := by
  have hc1 : pdE + 0x5000 < 2 ^ 47 := by decide
  have hmsb : (18446744073709551615#64).msb = true := by decide
  janus64_run [e2, hmsb] until [pdJ]
  exact ReachesRet.done (by rfl) ⟨rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- The inner copy loop: writes the `nd` digits held in `buf` (least significant at the end), with the separators, into `out`. -/
theorem pd_inner_loop (b D0 nd sepb z : Nat) (hsb : sepb < 256) (hb : 0x180 ≤ b) (hb2 : b + 0x198 ≤ 2 ^ 48)
    (hnd : nd ≤ 19) (hcb : cOf (D0 + nd) ≤ 132) :
    ∀ m, m ≤ nd → ∀ s : State, s.rip = BitVec.ofNat 64 pdI →
      s.mem.accessible (b + 83) 133 true = true → s.mem.accessible (b + 64) 19 true = true →
      s.regs 0 = BitVec.ofNat 64 (b + 0x40) → s.regs 2 = BitVec.ofNat 64 m - 1#64 → s.regs 4 = BitVec.ofNat 64 b →
      s.regs 11 = BitVec.ofNat 64 sepb → s.regs 12 = BitVec.ofNat 64 (132 - cOf (D0 + nd - m)) →
      s.regs 13 = BitVec.ofNat 64 (cOf (D0 + nd - m) % 4) →
      (∀ j, j < m → s.mem.readLE (b + 64 + j) 1 = 48 + z / 10 ^ (D0 + nd - 1 - j) % 10) →
      OutIs s.mem (b + 215) sepb z (cOf (D0 + nd - m)) →
      ReachesRet Fv256.PrettyProg.program (BitVec.ofNat 64 pdJ) s
        (fun S' => (∀ k, k ∉ [2, 12, 13, 15] → S'.regs k = s.regs k) ∧
          S'.regs 12 = BitVec.ofNat 64 (132 - cOf (D0 + nd)) ∧ S'.regs 13 = BitVec.ofNat 64 (cOf (D0 + nd) % 4) ∧
          S'.xmm = s.xmm ∧ S'.df = s.df ∧ MemFrame s.mem S'.mem [(b + 83, b + 216)] ∧
          OutIs S'.mem (b + 215) sepb z (cOf (D0 + nd))) := by
  intro m
  induction m with
  | zero =>
    intro hm s hpc hwa hbw e0 e2 e4 e11 e12 e13 hdig hout
    refine ReachesRet.mono (pd_inner_exit s hpc (by rw [e2]; decide)) ?_
    rintro S ⟨hr, hm', hx, hdf⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk; rw [hr]
    · rw [hr, e12]; simp
    · rw [hr, e13]; simp
    · exact hx
    · exact hdf
    · rw [hm']; exact MemFrame.refl _ _
    · rw [hm']; simpa using hout
  | succ m ih =>
    intro hm s hpc hwa hbw e0 e2 e4 e11 e12 e13 hdig hout
    have hD : D0 + nd - (m + 1) + 1 = D0 + nd - m := by omega
    have e2' : s.regs 2 = BitVec.ofNat 64 (m + 1 - 1) := by
      rw [e2]; exact Fv256.E.ofNat_sub_ofNat (m + 1) 1 (by omega) (by omega)
    have hcbD : cOf (D0 + nd - (m + 1) + 1) ≤ 132 := by
      have := cOf_mono (D0 + nd - (m + 1) + 1) (D0 + nd) (by omega)
      omega
    have hcD : cOf (D0 + nd - (m + 1)) ≤ 132 := by
      have := cOf_mono (D0 + nd - (m + 1)) (D0 + nd) (by omega)
      omega
    have hd1 := hdig m (by omega)
    rw [show D0 + nd - 1 - m = D0 + nd - (m + 1) by omega] at hd1
    refine Fv256.E.reachesRet_bind' (pd_inner_step s b (D0 + nd - (m + 1)) (m + 1) sepb z hpc (by omega) (by omega) hsb hcbD hb hb2
      hwa hbw e0 e2' e4 e11 e12 e13 hcD (by rw [show m + 1 - 1 = m by omega]; exact hd1) hout) ?_
    intro S hrip ⟨r0, r2, r11, r12, r13, rk, rx, rdf, hfr, hoS⟩
    rw [hD] at r12 r13 hoS
    have hfr1 := hfr
    refine ReachesRet.mono (ih (by omega) S hrip ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · rw [hfr.accessible]; exact hwa
    · rw [hfr.accessible]; exact hbw
    · rw [r0]; exact e0
    · rw [r2]; rw [show m + 1 - 1 = m by omega]
    · rw [rk 4 (by simp)]; exact e4
    · rw [r11]; exact e11
    · rw [r12]
    · rw [r13]
    · intro j hj
      rw [hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
      exact hdig j (by omega)
    · exact hoS
    · rintro S2 ⟨q1, q2, q3, q4, q5, q6, q7⟩
      refine ⟨?_, q2, q3, ?_, ?_, ?_, q7⟩
      · intro k hk; rw [q1 k hk, rk k hk]
      · rw [q4]; exact rx
      · rw [q5]; exact rdf
      · exact hfr.trans q6 (fun a n h => ⟨h, h⟩)
end Fv256.Amd64.Pd
