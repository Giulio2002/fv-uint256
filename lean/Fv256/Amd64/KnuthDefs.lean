import Fv256.ChainProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.KnuthMathB

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.KnuthDefs

/-- Register state at the head of the `udivremKnuth` outer loop (`k = j + 1`, `rsi = k - 1`). -/
def HeadR (R : Nat → W64) (k v n m up dp dl dh cap ql : Nat) (sp : W64) : Prop :=
  R 0 = BitVec.ofNat 64 v ∧ R 1 = BitVec.ofNat 64 (n - 1) ∧ R 3 = BitVec.ofNat 64 ql ∧ R 4 = sp ∧
  R 6 = BitVec.ofNat 64 k - 1 ∧ R 7 = BitVec.ofNat 64 up ∧ R 8 = BitVec.ofNat 64 cap ∧ R 9 = BitVec.ofNat 64 dp ∧
  R 10 = BitVec.ofNat 64 n ∧ R 11 = BitVec.ofNat 64 dl ∧ R 13 = BitVec.ofNat 64 m ∧ R 15 = BitVec.ofNat 64 dh

/-- Ranges written by one iteration with digit `j`. -/
def LRanges (up qp sp j m : Nat) : List (Nat × Nat) :=
  [(up + 8 * j, up + 8 * m), (qp + 8 * j, qp + 8 * j + 8), (sp, sp + 0x10), (sp + 0x18, sp + 0x30), (sp + 0x38, sp + 0x40)]

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
  hsp : sp + 0x90 ≤ 2 ^ 48
  hup : up + 8 * m ≤ 2 ^ 48
  hdp : dp + 8 * n ≤ 2 ^ 48
  hqp : qp + 8 * ql ≤ 2 ^ 48
  hdu : dp + 8 * n ≤ up ∨ up + 8 * m ≤ dp
  hds : dp + 8 * n ≤ sp ∨ sp + 0x90 ≤ dp
  hus : up + 8 * m ≤ sp ∨ sp + 0x90 ≤ up
  hqu : qp + 8 * ql ≤ up ∨ up + 8 * m ≤ qp
  hqs : qp + 8 * ql ≤ sp ∨ sp + 0x90 ≤ qp
  hqd : qp + 8 * ql ≤ dp ∨ dp + 8 * n ≤ qp
  hua : M0.accessible up (8 * m) true = true
  hda : M0.accessible dp (8 * n) false = true
  hqa : M0.accessible qp (8 * ql) true = true
  hsa : M0.accessible sp 0x90 true = true
  s10 : M0.readLE (sp + 0x10) 8 = v
  s30 : M0.readLE (sp + 0x30) 8 = dl
  s40 : M0.readLE (sp + 0x40) 8 = n - 1
  s58 : M0.readLE (sp + 0x58) 8 = qp
  s60 : M0.readLE (sp + 0x60) 8 = ql
  s80 : M0.readLE (sp + 0x80) 8 = cap
  s88 : M0.readLE (sp + 0x88) 8 = dp

/-- The loop invariant after the digits `≥ k` have been produced. -/
structure KInv (M0 M : Memory) (up dp qp n m sp k : Nat) : Prop where
  i1 : Fv256.B.wv M0 (up + 8 * k) (m - k) = Fv256.B.wv M0 dp n * Fv256.B.wv M (qp + 8 * k) (m - n - k) + Fv256.B.wv M (up + 8 * k) n
  i2 : Fv256.B.wv M (up + 8 * k) n < Fv256.B.wv M0 dp n
  fr : MemFrame M0 M [(up + 8 * k, up + 8 * m), (qp + 8 * k, qp + 8 * (m - n)), (sp, sp + 0x10), (sp + 0x18, sp + 0x30), (sp + 0x38, sp + 0x40)]


theorem kinv_finish (up dp qp n m ql v dl dh cap : Nat) (M0 M M' : Memory) (sp : Nat) (j qd rr : Nat)
    (K : KC up dp qp n m ql v dl dh cap sp M0) (hj : j + n + 1 ≤ m) (hI : KInv M0 M up dp qp n m sp (j + 1))
    (hFb : MemFrame M M' (LRanges up qp sp j m)) (hw1 : Fv256.B.wv M' (up + 8 * j) n = rr)
    (hrd : M'.readLE (qp + 8 * j) 8 = qd)
    (hdiv : Fv256.B.wv M0 dp n * qd + rr = Fv256.B.wv M (up + 8 * j) (n + 1)) (hrr : rr < Fv256.B.wv M0 dp n) :
    KInv M0 M' up dp qp n m sp j := by
  have hfr := hI.fr
  obtain ⟨hn, hn2, hm2, hmq, hql2, hdh, hdl, hdh63, hv, hcap, hcapB, hsp, hup, hdp, hqp, hdu, hds, hus, hqu, hqs, hqd, hua, hda, hqa, hsa, s10, s30, s40, s58, s60, s80, s88⟩ := K
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

end Fv256.Amd64.KnuthDefs
