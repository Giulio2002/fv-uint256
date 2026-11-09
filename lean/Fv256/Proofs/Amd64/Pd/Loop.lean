import Fv256.Proofs.Common.PrettyProg
import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.UtilE
import Fv256.Proofs.Common.PdCells
import Fv256.Proofs.Amd64.P.T
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.UtilB2
import Fv256.Proofs.Amd64.Pd.Chunk

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E Fv256.Amd64.P

namespace Fv256.Amd64.Pd

theorem z_small (z : Nat) (hz : z < 2 ^ 256) : z / 10 ^ (19 * 4 + 19) = 0 := by
  apply Nat.div_eq_of_lt
  have : (2:Nat) ^ 256 < 10 ^ (19 * 4 + 19) := by decide
  omega

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- The whole loop of `PrettyDec`, from the head with `t` chunks done to `pdF`. -/
theorem pd_loop (b z sepb : Nat) (hz1 : z < 2 ^ 256) (hsb : sepb < 256)
    (hb : 0x180 ≤ b) (hb8 : b % 8 = 0) (hb2 : b + 0x198 ≤ 2 ^ 48) :
    ∀ n t, t + n = 4 → ∀ (s : State), s.rip = BitVec.ofNat 64 pdH →
    z / 10 ^ (19 * t) ≠ 0 →
    s.mem.accessible (b - 0x180) (0x180 + 0x198) true = true → TabsOK s.mem →
    s.xmm 15 = 0 → s.df = false →
    s.regs 0 = BitVec.ofNat 64 19 → s.regs 1 = BitVec.ofNat 64 (132 - cOf (19 * t)) → s.regs 2 = BitVec.ofNat 64 (b + 0x40) →
    s.regs 6 = BitVec.ofNat 64 (cOf (19 * t) % 4) → s.regs 7 = BitVec.ofNat 64 (b + 0x130) → s.regs 9 = BitVec.ofNat 64 (b + 0x150) →
    s.regs 4 = BitVec.ofNat 64 b → s.regs 5 = BitVec.ofNat 64 (b + 0x178) →
    s.mem.readLE ((s.regs 14).toNat + 16) 8 + 0x100 < b → (s.regs 14).toNat + 24 ≤ 2 ^ 48 →
    s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true →
    ((s.regs 14).toNat + 16 + 8 ≤ b - 0x180 ∨ b + 0x198 ≤ (s.regs 14).toNat + 16) →
    Fv256.B.wv s.mem (b + 0x130) 4 = z / 10 ^ (19 * t) → Fv256.B.wv s.mem (b + 0x150) 4 = 10 ^ 19 →
    s.mem.readLE (b + 0x190) 1 = sepb → OutIs s.mem (b + 215) sepb z (cOf (19 * t)) →
    ReachesRet Fv256.PrettyProg.program (BitVec.ofNat 64 pdF) s
      (fun S' => S'.regs 12 = BitVec.ofNat 64 (132 - plen z) ∧
        S'.regs 4 = BitVec.ofNat 64 b ∧ S'.regs 5 = BitVec.ofNat 64 (b + 0x178) ∧ S'.regs 14 = s.regs 14 ∧
        S'.xmm 15 = 0 ∧ S'.df = false ∧
        MemFrame s.mem S'.mem [(b - 0x180, b + 376)] ∧ OutIs S'.mem (b + 215) sepb z (plen z) ∧ TabsOK S'.mem) := by
  intro n
  induction n with
  | zero =>
    intro t ht s hpc hy0 hw hd hx15 hdf e0 e1 e2 e6 e7 e9 e4 e5 hg3 hg1 hg2 hgd hym hdm hsep hout
    have ht4 : t = 4 := by omega
    subst ht4
    exact pd_chunk_final s b z (19 * 4) sepb s.mem hpc rfl hy0 (z_small z hz1) hz1 (by omega) hsb hb hb8 hb2 hw hd hx15 hdf
      e0 e1 e2 e6 e7 e9 e4 e5 hg3 hg1 hg2 hgd hym hdm hsep hout
  | succ n ih =>
    intro t ht s hpc hy0 hw hd hx15 hdf e0 e1 e2 e6 e7 e9 e4 e5 hg3 hg1 hg2 hgd hym hdm hsep hout
    by_cases hy' : z / 10 ^ (19 * t + 19) = 0
    · exact pd_chunk_final s b z (19 * t) sepb s.mem hpc rfl hy0 hy' hz1 (by omega) hsb hb hb8 hb2 hw hd hx15 hdf
        e0 e1 e2 e6 e7 e9 e4 e5 hg3 hg1 hg2 hgd hym hdm hsep hout
    · refine Fv256.E.reachesRet_bind' (pd_chunk_next s b z (19 * t) sepb s.mem hpc rfl hy0 hy' hz1 (by omega) hsb hb hb8 hb2 hw hd hx15 hdf
        e0 e1 e2 e6 e7 e9 e4 e5 hg3 hg1 hg2 hgd hym hdm hsep hout) ?_
      intro S hrip ⟨r0, r1, r2, r6, r7, r9, r4, r5, r14, rx, rdf, ry, rd, rfr, rout, rtab⟩
      have e19 : 19 * (t + 1) = 19 * t + 19 := by omega
      have hy1 : z / 10 ^ (19 * (t + 1)) ≠ 0 := by rw [e19]; exact hy'
      refine ReachesRet.mono (ih (t + 1) (by omega) S hrip hy1 ?_ ?_ rx rdf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
      · rw [rfr.accessible]; exact hw
      · exact rtab
      · rw [r0]
      · rw [e19]; exact r1
      · exact r2
      · rw [e19]; exact r6
      · exact r7
      · exact r9
      · exact r4
      · exact r5
      · rw [r14, rfr.readLE _ _ (by simp only [Outside, and_true]; omega)]; exact hg3
      · rw [r14]; exact hg1
      · rw [r14, rfr.accessible]; exact hg2
      · rw [r14]; exact hgd
      · rw [e19]; exact ry
      · exact rd
      · rw [rfr.readLE _ _ (by simp only [Outside, and_true]; omega)]; exact hsep
      · rw [e19]; exact rout
      · rintro S2 ⟨q12, q4, q5, q14, qx, qdf, qfr, qout, qtab⟩
        refine ⟨q12, q4, q5, ?_, qx, qdf, ?_, qout, qtab⟩
        · rw [q14, r14]
        · exact rfr.trans qfr (fun a n h => ⟨h, h⟩)
end Fv256.Amd64.Pd
