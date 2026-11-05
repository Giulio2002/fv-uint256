import Fv256.Arm64.ChainProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.Arm64.KnuthLem
import Fv256.Arm64.KnuthDefs
import Fv256.Arm64.KnuthLoop

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.KnuthEst Fv256.Arm64.KnuthDefs
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Fv256.Arm64.KnuthRun

set_option maxHeartbeats 8000000 in
/-- The whole outer loop: from the head with `k` digits left (`k ≤ m - n`) to the function epilogue (+0x1dc). -/
theorem knuth_loop (s0 : State) (up dp qp n m ql v dl dh cap : Nat) (M0 : Memory)
    (K : KC up dp qp n m ql v dl dh cap s0.sp.toNat M0) :
    ∀ k, k ≤ m - n → ∀ (R : Nat → W64) (fl : Flags) (M : Memory), HeadR R k v n m up dp dl dh cap →
      KInv M0 M up dp qp n m k →
      ReachesRet Fv256.Arm64.ChainProg.program (BitVec.ofNat 64 (kn + 0x1dc))
        { s0 with regs := R, pc := BitVec.ofNat 64 (kn + 0xbc), flags := fl, mem := M }
        (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
          S' = { s0 with regs := R', pc := BitVec.ofNat 64 (kn + 0x1dc), flags := fl', mem := M' } ∧
          KInv M0 M' up dp qp n m 0 ∧ (∀ i, i ∉ Scratch → i ≠ 3 → R' i = R i)) := by
  intro k
  induction k with
  | zero =>
    intro hk R fl M hR hI
    obtain ⟨r0, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ := hR
    have hneg : (R 3).getLsbD 63 = true := by rw [r3]; decide
    simp only [kn, reduceSegAddr, Nat.reduceAdd]
    janus_run [hneg]
    exact ⟨_, _, _, rfl, hI, fun i _ _ => rfl⟩
  | succ k ih =>
    intro hk R fl M hR hI
    have hit := Fv256.Arm64.KnuthLoop.iter s0 up dp qp n m ql v dl dh cap M0 R fl M k K (by omega) hR hI
    refine Fv256.B.reachesRet_trans hit ?_
    intro S' _ ⟨R', fl', M', hS', hR', hI', hpres⟩
    subst hS'
    refine Fv256.B.reachesRet_mono (ih (by omega) R' fl' M' hR' hI') ?_
    rintro S ⟨R'', fl'', M'', hS'', hI'', hp''⟩
    exact ⟨R'', fl'', M'', hS'', hI'', fun i h1 h2 => (hp'' i h1 h2).trans (hpres i h1 h2)⟩

end Fv256.Arm64.KnuthRun
