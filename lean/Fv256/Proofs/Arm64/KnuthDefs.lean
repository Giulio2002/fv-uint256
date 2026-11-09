import Fv256.Proofs.Arm64.ChainProg
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.KnuthMathB

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Fv256.Arm64.KnuthDefs

/-- Registers clobbered by one loop iteration (everything else is preserved). -/
def Scratch : List Nat := [1, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21]

/-- Register state at the head of the `udivremKnuth` outer loop (`k = j + 1` digits produced, `X3 = k - 1`). -/
def HeadR (R : Nat → W64) (k v n m up dp dl dh cap : Nat) : Prop :=
  R 0 = BitVec.ofNat 64 v ∧ R 2 = BitVec.ofNat 64 dh ∧ R 3 = BitVec.ofNat 64 k - 1#64 ∧ R 4 = BitVec.ofNat 64 dl ∧
  R 5 = BitVec.ofNat 64 m ∧ R 6 = BitVec.ofNat 64 dp ∧ R 7 = BitVec.ofNat 64 cap ∧ R 8 = BitVec.ofNat 64 n ∧
  R 9 = BitVec.ofNat 64 up ∧ R 10 = BitVec.ofNat 64 (n - 1)

/-- Ranges written by one iteration with digit `j`. -/
def LRanges (up qp j m : Nat) : List (Nat × Nat) :=
  [(up + 8 * j, up + 8 * m), (qp + 8 * j, qp + 8 * j + 8)]

/-- The constants of one `udivremKnuth` call, as seen in the memory `M0` at loop entry. -/
structure KC (up dp qp n m ql v dl dh cap sp : Nat) (M0 : Memory) : Prop where
  hn : 2 ≤ n
  hn2 : n < 2 ^ 20
  hm2 : m < 2 ^ 20
  hmq : m - n ≤ ql
  hql2 : ql < 2 ^ 20
  hdh : dh = M0.readLE (dp + 8 * (n - 1)) 8
  hdl : dl = M0.readLE (dp + 8 * (n - 2)) 8
  hdh63 : 2 ^ 63 ≤ dh
  hv : v + 2 ^ 64 = (2 ^ 64 * 2 ^ 64 - 1) / dh
  hcap : m ≤ cap
  hcapB : cap < 2 ^ 55
  hsp : sp % 16 = 0 ∧ sp + 120 ≤ 2 ^ 48
  hup : up + 8 * m ≤ 2 ^ 48
  hdp : dp + 8 * n ≤ 2 ^ 48
  hqp : qp + 8 * ql ≤ 2 ^ 48
  hdu : dp + 8 * n ≤ up ∨ up + 8 * m ≤ dp
  hqu : qp + 8 * ql ≤ up ∨ up + 8 * m ≤ qp
  hqd : qp + 8 * ql ≤ dp ∨ dp + 8 * n ≤ qp
  hus : up + 8 * m ≤ sp + 88 ∨ sp + 104 ≤ up
  hqs : qp + 8 * ql ≤ sp + 88 ∨ sp + 104 ≤ qp
  hua : M0.accessible up (8 * m) true = true
  hda : M0.accessible dp (8 * n) false = true
  hqa : M0.accessible qp (8 * ql) true = true
  hs88 : M0.accessible (sp + 88) 8 false = true
  hs96 : M0.accessible (sp + 96) 8 false = true
  s88 : M0.readLE (sp + 88) 8 = qp
  s96 : M0.readLE (sp + 96) 8 = ql

/-- The loop invariant after the digits `≥ k` have been produced. -/
structure KInv (M0 M : Memory) (up dp qp n m k : Nat) : Prop where
  i1 : Fv256.B.wv M0 (up + 8 * k) (m - k) = Fv256.B.wv M0 dp n * Fv256.B.wv M (qp + 8 * k) (m - n - k) + Fv256.B.wv M (up + 8 * k) n
  i2 : Fv256.B.wv M (up + 8 * k) n < Fv256.B.wv M0 dp n
  fr : MemFrame M0 M [(up + 8 * k, up + 8 * m), (qp + 8 * k, qp + 8 * (m - n))]

theorem kinv_finish (up dp qp n m ql v dl dh cap : Nat) (M0 M M' : Memory) (sp : Nat) (j qd rr : Nat)
    (K : KC up dp qp n m ql v dl dh cap sp M0) (hj : j + n + 1 ≤ m) (hI : KInv M0 M up dp qp n m (j + 1))
    (hFb : MemFrame M M' (LRanges up qp j m)) (hw1 : Fv256.B.wv M' (up + 8 * j) n = rr)
    (hrd : M'.readLE (qp + 8 * j) 8 = qd)
    (hdiv : Fv256.B.wv M0 dp n * qd + rr = Fv256.B.wv M (up + 8 * j) (n + 1)) (hrr : rr < Fv256.B.wv M0 dp n) :
    KInv M0 M' up dp qp n m j := by
  have hfr := hI.fr
  obtain ⟨hn, hn2, hm2, hmq, hql2, hdh, hdl, hdh63, hv, hcap, hcapB, hsp, hup, hdp, hqp, hdu, hqu, hqd, hus, hqs, hua, hda, hqa, hs88, hs96, s88, s96⟩ := K
  have hw2 : Fv256.B.wv M' (qp + 8 * (j + 1)) (m - n - (j + 1)) = Fv256.B.wv M (qp + 8 * (j + 1)) (m - n - (j + 1)) :=
    Fv256.B.wv_of_frame M _ _ hFb _ _ (by simp [LRanges, Outside]; omega)
  have huM : M0.readLE (up + 8 * j) 8 = M.readLE (up + 8 * j) 8 := (hfr.readLE _ _ (by simp [Outside]; omega)).symm
  have hXu : Fv256.B.wv M (up + 8 * j) (n + 1) =
      M.readLE (up + 8 * j) 8 + 2 ^ 64 * Fv256.B.wv M (up + 8 * (j + 1)) n := by
    rw [Fv256.B.wv_succ, show up + 8 * j + 8 = up + 8 * (j + 1) by omega]
  refine ⟨?_, ?_, ?_⟩
  · rw [show m - j = (m - (j + 1)) + 1 by omega, Fv256.B.wv_succ, show up + 8 * j + 8 = up + 8 * (j + 1) by omega,
      hI.i1, show m - n - j = (m - n - (j + 1)) + 1 by omega, Fv256.B.wv_succ, hrd, show qp + 8 * j + 8 = qp + 8 * (j + 1) by omega,
      hw2, hw1, huM]
    rw [hXu] at hdiv
    generalize Fv256.B.wv M0 dp n = D at *
    generalize Fv256.B.wv M (qp + 8 * (j + 1)) (m - n - (j + 1)) = Qp at *
    generalize Fv256.B.wv M (up + 8 * (j + 1)) n = Rr at *
    generalize M.readLE (up + 8 * j) 8 = uj at *
    grind
  · rw [hw1]; exact hrr
  · exact hfr.trans hFb (by intro a n' h; simp [LRanges, Outside] at h ⊢; omega)

end Fv256.Arm64.KnuthDefs
