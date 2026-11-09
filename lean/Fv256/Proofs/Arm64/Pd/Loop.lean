import Fv256.Proofs.Arm64.PrettyProg
import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.UtilE
import Fv256.Proofs.Common.UtilE64
import Fv256.Proofs.Common.PdCells
import Fv256.Proofs.Arm64.P.T
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.UtilB2
import Fv256.Proofs.Arm64.Pd.Chunk

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec
open Fv256.E Fv256.Arm64.P

namespace Fv256.Arm64.Pd

theorem z_small (z : Nat) (hz : z < 2 ^ 256) : z / 10 ^ (19 * 4 + 19) = 0 := by
  apply Nat.div_eq_of_lt
  have : (2:Nat) ^ 256 < 10 ^ (19 * 4 + 19) := by decide
  omega

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- The whole loop of `PrettyDec`, from the head with `t` chunks done to `pdF`. -/
theorem pd_loop (b z sepb : Nat) (hz1 : z < 2 ^ 256) (hsb : sepb < 256)
    (hb : 368 ≤ b) (hb16 : b % 16 = 0) (hb2 : b + 424 ≤ 2 ^ 48) :
    ∀ n t, t + n = 4 → ∀ (s : State), s.pc = BitVec.ofNat 64 pdH →
    z / 10 ^ (19 * t) ≠ 0 →
    s.mem.accessible (b - 368) (368 + 424) true = true → TabsOK s.mem →
    s.sp = BitVec.ofNat 64 b →
    s.regs 0 = 19#64 → s.regs 2 = BitVec.ofNat 64 (132 - cOf (19 * t)) → s.regs 3 = BitVec.ofNat 64 (b + 320) →
    s.regs 4 = BitVec.ofNat 64 (cOf (19 * t) % 4) → s.regs 6 = BitVec.ofNat 64 (b + 352) →
    s.regs 8 = BitVec.ofNat 64 (b + 80) →
    s.mem.readLE ((s.regs 28).toNat + 16) 8 + 304 < b → (s.regs 28).toNat + 24 ≤ 2 ^ 48 →
    s.mem.accessible ((s.regs 28).toNat + 16) 8 false = true →
    ((s.regs 28).toNat + 16 + 8 ≤ b - 368 ∨ b + 424 ≤ (s.regs 28).toNat + 16) →
    Fv256.B.wv s.mem (b + 320) 4 = z / 10 ^ (19 * t) → Fv256.B.wv s.mem (b + 352) 4 = 10 ^ 19 →
    s.mem.readLE (b + 416) 1 = sepb → OutIs s.mem (b + 231) sepb z (cOf (19 * t)) →
    ReachesRet Fv256.Arm64.PrettyProg.program (BitVec.ofNat 64 pdF) s
      (fun S' => S'.regs 10 = BitVec.ofNat 64 (132 - plen z) ∧
        S'.sp = s.sp ∧ S'.regs 28 = s.regs 28 ∧ S'.regs 29 = s.regs 29 ∧ S'.regs 18 = s.regs 18 ∧
        MemFrame s.mem S'.mem [(b - 368, b - 8), (b + 8, b + 392)] ∧ OutIs S'.mem (b + 231) sepb z (plen z) ∧ TabsOK S'.mem) := by
  intro n
  induction n with
  | zero =>
    intro t ht s hpc hy0 hw hd esp e0 e2 e3 e4 e6 e8 hg3 hg1 hg2 hgd hym hdm hsep hout
    have ht4 : t = 4 := by omega
    subst ht4
    exact pd_chunk_final s b z (19 * 4) sepb s.mem hpc rfl hy0 (z_small z hz1) hz1 (by omega) hsb hb hb16 hb2 hw hd esp
      e0 e2 e3 e4 e6 e8 hg3 hg1 hg2 hgd hym hdm hsep hout
  | succ n ih =>
    intro t ht s hpc hy0 hw hd esp e0 e2 e3 e4 e6 e8 hg3 hg1 hg2 hgd hym hdm hsep hout
    by_cases hy' : z / 10 ^ (19 * t + 19) = 0
    · exact pd_chunk_final s b z (19 * t) sepb s.mem hpc rfl hy0 hy' hz1 (by omega) hsb hb hb16 hb2 hw hd esp
        e0 e2 e3 e4 e6 e8 hg3 hg1 hg2 hgd hym hdm hsep hout
    · refine Fv256.E.reachesRet64_bind (pd_chunk_next s b z (19 * t) sepb s.mem hpc rfl hy0 hy' hz1 (by omega) hsb hb hb16 hb2 hw hd esp
        e0 e2 e3 e4 e6 e8 hg3 hg1 hg2 hgd hym hdm hsep hout) ?_
      intro S hrip ⟨r0, r2, r8, r4, r3, r6, rsp, r28, r29, r18, ry, rd, rsep, rfr, rout, rtab⟩
      have e19 : 19 * (t + 1) = 19 * t + 19 := by omega
      have hy1 : z / 10 ^ (19 * (t + 1)) ≠ 0 := by rw [e19]; exact hy'
      refine Fv256.E.reachesRet64_mono (ih (t + 1) (by omega) S hrip hy1 ?_ ?_ ?_ r0 ?_ r3 ?_ r6 r8 ?_ ?_ ?_ ?_ ?_ ?_ rsep ?_) ?_
      · rw [rfr.accessible]; exact hw
      · exact rtab
      · rw [rsp]; exact esp
      · rw [e19]; exact r2
      · rw [e19]; exact r4
      · rw [r28, rfr.readLE _ _ (by simp only [Outside, and_true]; omega)]; exact hg3
      · rw [r28]; exact hg1
      · rw [r28, rfr.accessible]; exact hg2
      · rw [r28]; exact hgd
      · rw [e19]; exact ry
      · exact rd
      · rw [e19]; exact rout
      · rintro S2 ⟨q10, qsp, q28, q29, q18, qfr, qout, qtab⟩
        refine ⟨q10, ?_, ?_, ?_, ?_, ?_, qout, qtab⟩
        · rw [qsp, rsp]
        · rw [q28, r28]
        · rw [q29, r29]
        · rw [q18, r18]
        · exact rfr.trans qfr (fun a n h => ⟨h, h⟩)
end Fv256.Arm64.Pd
