import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.KnuthMathB
import Fv256.Arm64.KnuthDefs
import Fv256.Arm64.Div64
import Fv256.Arm64.KnuthLem
import Fv256.Arm64.KnuthEntry
import Fv256.Arm64.KnuthRun
import Fv256.Arm64.KnuthExit

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.KnuthDefs
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Fv256.Arm64.KnuthSummary
abbrev kn : Nat := segAddr Extracted.program "github.com/holiman/uint256.udivremKnuth"

/-- `udivremKnuth(quot, u, d []uint64)` (arm64 ABI: quot = X0/X1/X2, u = X3/X4/X5, d = X6/X7/X8). Let `m = len u = X4`,
`n = len d = X7`, `ql = len quot = X1`, `cap = cap u = X5`. Precondition: `2 <= n <= m < 2^20`, `m <= cap < 2^55`, `m - n <= ql < 2^20`,
the top word of `d` is normalised (`>= 2^63`), the top `n` words of `u` are `< d`. Postcondition: `u = d * quot + u'`, `u' < d`
(`u'` = the low `n` words of `u` afterwards). -/
theorem knuth_summary :
    Summary Extracted.program kn
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 80 ∧ StackOK s 120 72 ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 120 ∨ s.sp.toNat + 72 ≤ (s.regs 28).toNat + 16) ∧
        2 ≤ (s.regs 7).toNat ∧ (s.regs 7).toNat ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat < 2 ^ 20 ∧
        (s.regs 4).toNat ≤ (s.regs 5).toNat ∧ (s.regs 5).toNat < 2 ^ 55 ∧
        (s.regs 4).toNat - (s.regs 7).toNat ≤ (s.regs 1).toNat ∧ (s.regs 1).toNat < 2 ^ 20 ∧
        (s.regs 3).toNat + 8 * (s.regs 4).toNat ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 3).toNat (8 * (s.regs 4).toNat) true = true ∧
        (s.regs 6).toNat + 8 * (s.regs 7).toNat ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 6).toNat (8 * (s.regs 7).toNat) false = true ∧
        (s.regs 0).toNat + 8 * (s.regs 1).toNat ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat (8 * (s.regs 1).toNat) true = true ∧
        ((s.regs 6).toNat + 8 * (s.regs 7).toNat ≤ (s.regs 3).toNat ∨ (s.regs 3).toNat + 8 * (s.regs 4).toNat ≤ (s.regs 6).toNat) ∧
        ((s.regs 0).toNat + 8 * (s.regs 1).toNat ≤ (s.regs 3).toNat ∨ (s.regs 3).toNat + 8 * (s.regs 4).toNat ≤ (s.regs 0).toNat) ∧
        ((s.regs 0).toNat + 8 * (s.regs 1).toNat ≤ (s.regs 6).toNat ∨ (s.regs 6).toNat + 8 * (s.regs 7).toNat ≤ (s.regs 0).toNat) ∧
        ((s.regs 3).toNat + 8 * (s.regs 4).toNat ≤ s.sp.toNat - 120 ∨ s.sp.toNat + 72 ≤ (s.regs 3).toNat) ∧
        ((s.regs 6).toNat + 8 * (s.regs 7).toNat ≤ s.sp.toNat - 120 ∨ s.sp.toNat + 72 ≤ (s.regs 6).toNat) ∧
        ((s.regs 0).toNat + 8 * (s.regs 1).toNat ≤ s.sp.toNat - 120 ∨ s.sp.toNat + 72 ≤ (s.regs 0).toNat) ∧
        2 ^ 63 ≤ s.mem.readLE ((s.regs 6).toNat + 8 * ((s.regs 7).toNat - 1)) 8 ∧
        Fv256.B.wv s.mem ((s.regs 3).toNat + 8 * ((s.regs 4).toNat - (s.regs 7).toNat)) (s.regs 7).toNat <
          Fv256.B.wv s.mem (s.regs 6).toNat (s.regs 7).toNat)
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧ (∀ i, 22 ≤ i → s'.regs i = s.regs i) ∧
        Fv256.B.wv s.mem (s.regs 3).toNat (s.regs 4).toNat =
          Fv256.B.wv s.mem (s.regs 6).toNat (s.regs 7).toNat * Fv256.B.wv s'.mem (s.regs 0).toNat ((s.regs 4).toNat - (s.regs 7).toNat) +
            Fv256.B.wv s'.mem (s.regs 3).toNat (s.regs 7).toNat ∧
        Fv256.B.wv s'.mem (s.regs 3).toNat (s.regs 7).toNat < Fv256.B.wv s.mem (s.regs 6).toNat (s.regs 7).toNat ∧
        MemFrame s.mem s'.mem [((s.regs 3).toNat, (s.regs 3).toNat + 8 * (s.regs 4).toNat),
          ((s.regs 0).toNat, (s.regs 0).toNat + 8 * ((s.regs 4).toNat - (s.regs 7).toNat)),
          (s.sp.toNat - 120, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 72)]) := by
  intro s hpc ⟨h30a, h30b, hg, hso, hgs, hn, hnm, hm2, hcm, hcapB, hmq, hql2, hub, hua, hdb, hda, hqb, hqa, hdu, hqu, hqd, hus, hds, hqs, hdh63, hD⟩
  have e0 : s.regs 0 = BitVec.ofNat 64 (s.regs 0).toNat := by simp
  have e1 : s.regs 1 = BitVec.ofNat 64 (s.regs 1).toNat := by simp
  have e3 : s.regs 3 = BitVec.ofNat 64 (s.regs 3).toNat := by simp
  have e4 : s.regs 4 = BitVec.ofNat 64 (s.regs 4).toNat := by simp
  have e5 : s.regs 5 = BitVec.ofNat 64 (s.regs 5).toNat := by simp
  have e6 : s.regs 6 = BitVec.ofNat 64 (s.regs 6).toNat := by simp
  have e7 : s.regs 7 = BitVec.ofNat 64 (s.regs 7).toNat := by simp
  obtain ⟨hal, hsb, hsa, hsw⟩ := hso
  obtain ⟨dh, hdhr⟩ : ∃ dh, s.mem.readLE ((s.regs 6).toNat + 8 * ((s.regs 7).toNat - 1)) 8 = dh := ⟨_, rfl⟩
  obtain ⟨dl, hdlr⟩ : ∃ dl, s.mem.readLE ((s.regs 6).toNat + 8 * ((s.regs 7).toNat - 2)) 8 = dl := ⟨_, rfl⟩
  rw [hdhr] at hdh63
  generalize hqp : (s.regs 0).toNat = qp at *
  generalize hql : (s.regs 1).toNat = ql at *
  generalize hup : (s.regs 3).toNat = up at *
  generalize hm : (s.regs 4).toNat = m at *
  generalize hcap : (s.regs 5).toNat = cap at *
  generalize hdp : (s.regs 6).toNat = dp at *
  generalize hn' : (s.regs 7).toNat = n at *
  have hdhB : dh < 2 ^ 64 := by rw [← hdhr]; have := Janus.Arm64.Memory.readLE_lt s.mem (dp + 8 * (n - 1)) 8; simpa using this
  have hsp80 : 80 ≤ s.sp.toNat := by omega
  have h1 := Fv256.Arm64.KnuthEntry.knuth_entry s up dp qp n m ql cap dh dl h30a h30b hg ⟨hal, hsb, hsa, hsw⟩ hgs hn hnm hm2 hcm hcapB hmq hql2
    hub hua hdb hda hqb hqa hdu hqu hqd hus hds hqs hdh63 hdhr hdlr e0 e1 e3 e4 e5 e6 e7 hpc
  refine Fv256.B.reachesRet_trans h1 ?_
  intro S1 hrip ⟨hpc1, hsp1, ⟨v, hv, hHead⟩, r18, r28, r29, rpres, hfr1, mfp, mlr, mqp, mql⟩
  have hS1sp : S1.sp.toNat = s.sp.toNat - 80 := by
    rw [hsp1, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; have := s.sp.isLt; omega
  have hread : ∀ a k, Outside a k [(s.sp.toNat - 120, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 72)] →
      S1.mem.readLE a k = s.mem.readLE a k := fun a k h => hfr1.readLE a k h
  have hstk : s.mem.accessible (s.sp.toNat - 120) (120 + 72) true = true := hsw
  have hstkr : ∀ a k, s.sp.toNat - 120 ≤ a → a + k ≤ s.sp.toNat + 72 → s.mem.accessible a k false = true := fun a k h1 h2 =>
    Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hstk) (by omega) (by omega)
  have K : KC up dp qp n m ql v dl dh cap S1.sp.toNat S1.mem := by
    rw [hS1sp]
    refine ⟨hn, by omega, hm2, hmq, hql2, ?_, ?_, hdh63, hv, hcm, hcapB, ⟨by omega, by omega⟩, by omega, by omega, by omega, hdu, hqu, hqd,
      by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hread _ _ (by simp [Outside]; omega)]; exact hdhr.symm
    · rw [hread _ _ (by simp [Outside]; omega)]; exact hdlr.symm
    · rw [hfr1.accessible]; exact hua
    · rw [hfr1.accessible]; exact hda
    · rw [hfr1.accessible]; exact hqa
    · rw [hfr1.accessible]; exact hstkr _ _ (by omega) (by omega)
    · rw [hfr1.accessible]; exact hstkr _ _ (by omega) (by omega)
    · rw [show s.sp.toNat - 80 + 88 = s.sp.toNat + 8 by omega]; exact mqp
    · rw [show s.sp.toNat - 80 + 96 = s.sp.toNat + 16 by omega]; exact mql
  have hwu : Fv256.B.wv S1.mem up m = Fv256.B.wv s.mem up m :=
    Fv256.B.wv_of_frame s.mem S1.mem _ hfr1 up m (by simp [Outside]; omega)
  have hwd : Fv256.B.wv S1.mem dp n = Fv256.B.wv s.mem dp n :=
    Fv256.B.wv_of_frame s.mem S1.mem _ hfr1 dp n (by simp [Outside]; omega)
  have hwt : Fv256.B.wv S1.mem (up + 8 * (m - n)) n = Fv256.B.wv s.mem (up + 8 * (m - n)) n :=
    Fv256.B.wv_of_frame s.mem S1.mem _ hfr1 (up + 8 * (m - n)) n (by simp [Outside]; omega)
  have hI0 : KInv S1.mem S1.mem up dp qp n m (m - n) := by
    refine ⟨?_, ?_, MemFrame.refl _ _⟩
    · rw [show m - (m - n) = n by omega, show m - n - (m - n) = 0 by omega]; simp [Fv256.B.wv]
    · rw [hwt, hwd]; exact hD
  have hrip' : ({ S1 with regs := S1.regs, pc := BitVec.ofNat 64 (kn + 0xbc), flags := S1.flags, mem := S1.mem } : State) = S1 := by
    rw [← hpc1]
  have h2 := Fv256.Arm64.KnuthRun.knuth_loop S1 up dp qp n m ql v dl dh cap S1.mem K (m - n) (Nat.le_refl _) S1.regs S1.flags S1.mem hHead hI0
  rw [hrip'] at h2
  refine Fv256.B.reachesRet_trans h2 ?_
  intro S2 hrip2 ⟨R2, fl2, M2, hS2, hI2, hp2⟩
  subst hS2
  have hfr2 := hI2.fr
  have hexit := Fv256.Arm64.KnuthExit.knuth_exit { S1 with regs := R2, pc := BitVec.ofNat 64 (kn + 0x1dc), flags := fl2, mem := M2 }
    (s.regs 30) (s.regs 29).toNat M2 (by show S1.sp.toNat % 16 = 0; omega) (by show 8 ≤ S1.sp.toNat; omega)
    (by show S1.sp.toNat + 80 ≤ 2 ^ 48; omega) rfl rfl
    (by show M2.readLE S1.sp.toNat 8 = _; rw [hfr2.readLE _ _ (by simp [Outside]; omega), hS1sp]; exact mlr)
    (by show M2.readLE (S1.sp.toNat - 8) 8 = _; rw [hfr2.readLE _ _ (by simp [Outside]; omega), hS1sp,
          show s.sp.toNat - 80 - 8 = s.sp.toNat - 88 by omega]; exact mfp)
    h30a h30b
    (by show M2.accessible S1.sp.toNat 8 false = true; rw [hfr2.accessible, hfr1.accessible]; exact hstkr _ _ (by omega) (by omega))
    (by show M2.accessible (S1.sp.toNat - 8) 8 false = true; rw [hfr2.accessible, hfr1.accessible]; exact hstkr _ _ (by omega) (by omega))
  refine Fv256.B.reachesRet_mono hexit ?_
  intro S' ⟨q1, q2, q3, q4, q5, q6⟩
  have hi1 := hI2.i1
  have hi2 := hI2.i2
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at hi1 hi2
  rw [hwu, hwd] at hi1
  rw [hwd] at hi2
  have hS'sp : S'.sp = s.sp := by rw [q2]; show S1.sp + 80#64 = s.sp; rw [hsp1]; bv_omega
  refine ⟨q1, hS'sp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [q5 18 (by omega) (by omega)]; show R2 18 = _
    rw [hp2 18 (by simp [Scratch]) (by omega)]; exact r18
  · rw [q5 28 (by omega) (by omega)]; show R2 28 = _
    rw [hp2 28 (by simp [Scratch]) (by omega)]; exact r28
  · rw [q3]; simp
  · exact q4
  · intro i h22
    by_cases h29 : i = 29
    · subst h29; rw [q3]; simp
    · by_cases h30 : i = 30
      · subst h30; exact q4
      · rw [q5 i h29 h30]; show R2 i = _
        rw [hp2 i (by simp [Scratch]; omega) (by omega)]; exact rpres i h22 h29 h30
  · rw [q6]
    simp only [hqp, hup, hm, hdp, hn']
    refine ⟨hi1, hi2, ?_⟩
    exact hfr1.trans hfr2 (by intro a k h; simp [Outside] at h ⊢; omega)

end Fv256.Arm64.KnuthSummary
