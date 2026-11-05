import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.Arm64.KnuthLem
import Fv256.Arm64.KnuthDefs
import Fv256.Arm64.Div64

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.KnuthDefs Fv256.Arm64.KnuthLem
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Fv256.Arm64.KnuthEntry
abbrev kn : Nat := segAddr Extracted.program "github.com/holiman/uint256.udivremKnuth"

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem knuth_entry (s : State) (up dp qp n m ql cap dh dl : Nat)
    (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 56)
    (hg : GuardOK s 80) (hso : StackOK s 120 72)
    (hgs : (s.regs 28).toNat + 24 ≤ s.sp.toNat - 120 ∨ s.sp.toNat + 72 ≤ (s.regs 28).toNat + 16)
    (hn : 2 ≤ n) (hnm : n ≤ m) (hm2 : m < 2 ^ 20) (hcm : m ≤ cap) (hcapB : cap < 2 ^ 55)
    (hmq : m - n ≤ ql) (hql2 : ql < 2 ^ 20)
    (hub : up + 8 * m ≤ 2 ^ 48) (hua : s.mem.accessible up (8 * m) true = true)
    (hdb : dp + 8 * n ≤ 2 ^ 48) (hda : s.mem.accessible dp (8 * n) false = true)
    (hqb : qp + 8 * ql ≤ 2 ^ 48) (hqa : s.mem.accessible qp (8 * ql) true = true)
    (hdu : dp + 8 * n ≤ up ∨ up + 8 * m ≤ dp) (hqu : qp + 8 * ql ≤ up ∨ up + 8 * m ≤ qp) (hqd : qp + 8 * ql ≤ dp ∨ dp + 8 * n ≤ qp)
    (hus : up + 8 * m ≤ s.sp.toNat - 120 ∨ s.sp.toNat + 72 ≤ up)
    (hds : dp + 8 * n ≤ s.sp.toNat - 120 ∨ s.sp.toNat + 72 ≤ dp)
    (hqs : qp + 8 * ql ≤ s.sp.toNat - 120 ∨ s.sp.toNat + 72 ≤ qp)
    (hdh63 : 2 ^ 63 ≤ dh) (hdhr : s.mem.readLE (dp + 8 * (n - 1)) 8 = dh) (hdlr : s.mem.readLE (dp + 8 * (n - 2)) 8 = dl)
    (e0 : s.regs 0 = BitVec.ofNat 64 qp) (e1 : s.regs 1 = BitVec.ofNat 64 ql) (e3 : s.regs 3 = BitVec.ofNat 64 up)
    (e4 : s.regs 4 = BitVec.ofNat 64 m) (e5 : s.regs 5 = BitVec.ofNat 64 cap) (e6 : s.regs 6 = BitVec.ofNat 64 dp)
    (e7 : s.regs 7 = BitVec.ofNat 64 n)
    (hpc : s.pc = BitVec.ofNat 64 kn) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (kn + 0xbc)) s (fun S => S.pc = BitVec.ofNat 64 (kn + 0xbc) ∧ S.sp = s.sp - 80#64 ∧
        (∃ v, v + 2 ^ 64 = (2 ^ 64 * 2 ^ 64 - 1) / dh ∧ HeadR S.regs (m - n) v n m up dp dl dh cap) ∧
        S.regs 18 = s.regs 18 ∧ S.regs 28 = s.regs 28 ∧ S.regs 29 = s.sp - 88#64 ∧
        (∀ i, 22 ≤ i → i ≠ 29 → i ≠ 30 → S.regs i = s.regs i) ∧
        MemFrame s.mem S.mem [(s.sp.toNat - 120, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 72)] ∧
        S.mem.readLE (s.sp.toNat - 88) 8 = (s.regs 29).toNat ∧ S.mem.readLE (s.sp.toNat - 80) 8 = (s.regs 30).toNat ∧
        S.mem.readLE (s.sp.toNat + 8) 8 = qp ∧ S.mem.readLE (s.sp.toNat + 16) 8 = ql) := by
  have hdhB : dh < 2 ^ 64 := by rw [← hdhr]; have := Janus.Arm64.Memory.readLE_lt s.mem (dp + 8 * (n - 1)) 8; simpa using this
  have hnot : (~~~BitVec.ofNat 64 dh).toNat < dh := by
    rw [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdhB]; omega
  obtain ⟨hal, hsb, hsa, hsw⟩ := hso
  obtain ⟨hg1, hg2, hg3⟩ := hg
  simp only [kn, reduceSegAddr, Nat.reduceAdd] at *
  janus_run [e0, e1, e3, e4, e5, e6, e7, hdhr, hdlr] until [kn + 0xbc] calls [Fv256.Arm64.Div64.div64_summary]
  rename_i _ _ _ _ _ _ _ _ _ hr0 _ hpres hpfr
  have hdlB : dl < 2 ^ 64 := by rw [← hdlr]; have := Janus.Arm64.Memory.readLE_lt s.mem (dp + 8 * (n - 2)) 8; simpa using this
  refine ⟨⟨(s'.regs 0).toNat, ?_, ?_⟩, ?_, ?_⟩
  · rw [hr0, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdhB]
    exact recip_eq dh hdh63 hdhB
  · have hd : dl % 18446744073709551616 = dl := Nat.mod_eq_of_lt hdlB
    have hmn : (18446744073709551616 - n + m) % 18446744073709551616 = m - n := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try simp (config := { decide := true }) only [setReg_apply, ↓reduceIte, hd, hmn])
    all_goals (try simp)
  · intro i h22 h29 h30
    rw [hpres i (by simp; omega)]
    try simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
    simp only [show ¬ i = 10 by omega, show ¬ i = 9 by omega, show ¬ i = 8 by omega, show ¬ i = 7 by omega,
      show ¬ i = 6 by omega, show ¬ i = 5 by omega, show ¬ i = 4 by omega, show ¬ i = 3 by omega, show ¬ i = 2 by omega,
      show ¬ i = 30 by omega, show ¬ i = 29 by omega, show ¬ i = 16 by omega, show ¬ i = 1 by omega, show ¬ i = 0 by omega, if_false]
  · janus_frame
end Fv256.Arm64.KnuthEntry
