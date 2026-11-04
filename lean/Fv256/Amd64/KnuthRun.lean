import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.KnuthMathB
import Fv256.Amd64.KnuthSub
import Fv256.Amd64.KnuthDefs
import Fv256.Amd64.KnuthLoop

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.KnuthSub Fv256.Amd64.KnuthDefs

namespace Fv256.Amd64.KnuthRun

set_option maxHeartbeats 8000000 in
theorem knuth_loop (s0 : State) (up dp qp n m ql v dl dh cap : Nat) (M0 : Memory) (sp : W64)
    (K : KC up dp qp n m ql v dl dh cap sp.toNat M0) :
    ∀ k, k ≤ m - n → ∀ (R : Nat → W64) (fl : Flags) (M : Memory), HeadR R k v n m up dp dl dh cap ql sp →
      KInv M0 M up dp qp n m sp.toNat k →
      ReachesRet Extracted.program (BitVec.ofNat 64 (kn + 0x26b))
        { s0 with regs := R, rip := BitVec.ofNat 64 (kn + 0xd1), flags := fl, mem := M }
        (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
          S' = { s0 with regs := R', rip := BitVec.ofNat 64 (kn + 0x26b), flags := fl', mem := M' } ∧
          R' 4 = sp ∧ KInv M0 M' up dp qp n m sp.toNat 0 ∧ R' 14 = R 14) := by
  intro k
  induction k with
  | zero =>
    intro hk R fl M hR hI
    obtain ⟨r0, r1, r3, r4, r6, r7, r8, r9, r10, r11, r13, r15⟩ := hR
    have hcode := kn_lt
    have hneg : (R 6).msb = true := by rw [r6]; decide
    janus64_run [hneg]
    exact ⟨_, _, _, rfl, r4, hI, rfl⟩
  | succ k ih =>
    intro hk R fl M hR hI
    have hit := Fv256.Amd64.KnuthLoop.iter s0 up dp qp n m ql v dl dh cap M0 R sp fl M k K (by omega) hR hI
    refine Fv256.B.reachesRet_trans64 hit ?_
    intro S' _ ⟨R', fl', M', hS', hR', hI', h14⟩
    subst hS'
    refine Fv256.B.reachesRet_mono64 (ih (by omega) R' fl' M' hR' hI') ?_
    rintro S ⟨R'', fl'', M'', hS'', h4'', hI'', h14''⟩
    exact ⟨R'', fl'', M'', hS'', h4'', hI'', h14''.trans h14⟩

end Fv256.Amd64.KnuthRun
