import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.KnuthMathB
import Fv256.Amd64.KnuthSub
import Fv256.Amd64.KnuthDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.KnuthSub Fv256.Amd64.KnuthDefs

namespace Fv256.Amd64.KnuthEntry

set_option maxHeartbeats 8000000 in
theorem knuth_entry (s : State) (up dp qp n m ql cap dh dl : Nat)
    (hg : StackGuardOK s 0) (hn : 2 ≤ n) (hn2 : n < 2 ^ 20) (hnm : n ≤ m) (hm2 : m < 2 ^ 20)
    (hqp : (s.regs 0).toNat = qp) (hql : (s.regs 3).toNat = ql) (hup : (s.regs 7).toNat = up) (hm : (s.regs 6).toNat = m)
    (hcap : (s.regs 8).toNat = cap) (hdp' : (s.regs 9).toNat = dp) (hn' : (s.regs 10).toNat = n)
    (hdh : s.mem.readLE (dp + n * 8 - 8) 8 = dh) (hdl : s.mem.readLE (dp + n * 8 - 16) 8 = dl)
    (hdh63 : 2 ^ 63 ≤ dh)
    (hdp : dp + 8 * n ≤ 2 ^ 48) (hda : s.mem.accessible dp (8 * n) false = true)
    (hw : StackWritable s 0x50 0x40) (hdisj : dp + 8 * n ≤ (s.regs 4).toNat - 0x50 ∨ (s.regs 4).toNat + 0x40 ≤ dp) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (kn + 0xd1)) { s with rip := BitVec.ofNat 64 kn }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory) (v : Nat),
        S' = { s with regs := R', rip := BitVec.ofNat 64 (kn + 0xd1), flags := fl', mem := M' } ∧
        v + 2 ^ 64 = (2 ^ 64 * 2 ^ 64 - 1) / dh ∧
        Fv256.Amd64.KnuthDefs.HeadR R' (m - n) v n m up dp dl dh cap ql (s.regs 4 - 80#64) ∧
        (∀ k, k ∉ [0, 1, 2, 3, 4, 5, 6, 11, 12, 13, 15] → R' k = s.regs k) ∧
        M'.readLE ((s.regs 4).toNat - 64) 8 = v ∧ M'.readLE ((s.regs 4).toNat - 32) 8 = dl ∧
        M'.readLE ((s.regs 4).toNat - 16) 8 = n - 1 ∧ M'.readLE ((s.regs 4).toNat + 8) 8 = qp ∧
        M'.readLE ((s.regs 4).toNat + 16) 8 = ql ∧ M'.readLE ((s.regs 4).toNat + 48) 8 = cap ∧
        M'.readLE ((s.regs 4).toNat + 56) 8 = dp ∧ M'.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧
        MemFrame s.mem M' [((s.regs 4).toNat - 0x50, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 0x40)]) := by
  have hcode := kn_lt
  obtain ⟨hlow, hnw, hacc⟩ := hw
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgr hgb hgl hnw2 hacc hlow hnw
  have hdh' : s.mem.readLE ((s.regs 9).toNat + (s.regs 10).toNat * 8 - 8) 8 = dh := by rw [hdp', hn']; exact hdh
  have hdl' : s.mem.readLE ((s.regs 9).toNat + (s.regs 10).toNat * 8 - 16) 8 = dl := by rw [hdp', hn']; exact hdl
  have hd2 : dh < 2 ^ 64 := by
    rw [← hdh]; have := Janus.Arm64.Memory.readLE_lt s.mem (dp + n * 8 - 8) 8; simpa using this
  have hdivlt : ¬ (18446744073709551616 ≤ ((18446744073709551615 - dh) * 18446744073709551616 + 18446744073709551615) / dh) := by
    refine Nat.not_le.mpr (Nat.div_lt_of_lt_mul ?_)
    have : (18446744073709551615 - dh + 1) * 18446744073709551616 ≤ dh * 18446744073709551616 :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul] at this
    rw [Nat.mul_comm dh]
    omega
  have hdivlt' : ¬ (18446744073709551616 ≤ ((18446744073709551615 - s.mem.readLE ((s.regs 9).toNat + (s.regs 10).toNat * 8 - 8) 8) * 18446744073709551616 + 18446744073709551615) / s.mem.readLE ((s.regs 9).toNat + (s.regs 10).toNat * 8 - 8) 8) := by
    rw [hdh']; exact hdivlt
  have hdh63' : 2 ^ 63 ≤ s.mem.readLE ((s.regs 9).toNat + (s.regs 10).toNat * 8 - 8) 8 := by rw [hdh']; exact hdh63
  janus64_run [BitVec.toNat_not, hdivlt'] until [kn + 0xd1]
  have e0 : s.regs 0 = BitVec.ofNat 64 qp := by apply BitVec.eq_of_toNat_eq; rw [hqp, BitVec.toNat_ofNat]; have := (s.regs 0).isLt; omega
  have e3 : s.regs 3 = BitVec.ofNat 64 ql := by apply BitVec.eq_of_toNat_eq; rw [hql, BitVec.toNat_ofNat]; have := (s.regs 3).isLt; omega
  have e6 : s.regs 6 = BitVec.ofNat 64 m := by apply BitVec.eq_of_toNat_eq; rw [hm, BitVec.toNat_ofNat]; have := (s.regs 6).isLt; omega
  have e7 : s.regs 7 = BitVec.ofNat 64 up := by apply BitVec.eq_of_toNat_eq; rw [hup, BitVec.toNat_ofNat]; have := (s.regs 7).isLt; omega
  have e8 : s.regs 8 = BitVec.ofNat 64 cap := by apply BitVec.eq_of_toNat_eq; rw [hcap, BitVec.toNat_ofNat]; have := (s.regs 8).isLt; omega
  have e9 : s.regs 9 = BitVec.ofNat 64 dp := by apply BitVec.eq_of_toNat_eq; rw [hdp', BitVec.toNat_ofNat]; have := (s.regs 9).isLt; omega
  have e10 : s.regs 10 = BitVec.ofNat 64 n := by apply BitVec.eq_of_toNat_eq; rw [hn', BitVec.toNat_ofNat]; have := (s.regs 10).isLt; omega
  have hvrel : ((18446744073709551615 - dh) * 18446744073709551616 + 18446744073709551615) / dh + 2 ^ 64 =
      (2 ^ 64 * 2 ^ 64 - 1) / dh := by
    have hd0 : 0 < dh := by omega
    have e : (2 ^ 64 * 2 ^ 64 - 1 : Nat) = (18446744073709551615 - dh) * 18446744073709551616 + 18446744073709551615 +
        dh * 18446744073709551616 := by
      have : dh * 18446744073709551616 ≤ 2 ^ 64 * 2 ^ 64 - 1 := by
        have := Nat.mul_le_mul_right 18446744073709551616 (show dh ≤ 18446744073709551615 by omega)
        omega
      have e2 : (18446744073709551615 - dh) * 18446744073709551616 + dh * 18446744073709551616 = 18446744073709551615 * 18446744073709551616 := by
        rw [← Nat.add_mul]; congr 1; omega
      omega
    rw [e, Nat.mul_comm dh 18446744073709551616, Nat.add_mul_div_right _ _ hd0]
  have hdlB : dl < 2 ^ 64 := by
    rw [← hdl]; have := Janus.Arm64.Memory.readLE_lt s.mem (dp + n * 8 - 16) 8; simpa using this
  have i0 := (s.regs 0).isLt
  have i3 := (s.regs 3).isLt
  have i5 := (s.regs 5).isLt
  have i8 := (s.regs 8).isLt
  have i9 := (s.regs 9).isLt
  have i10 := (s.regs 10).isLt
  simp only [Nat.reducePow] at i0 i3 i5 i8 i9 i10 hdlB
  have hvB : ((18446744073709551615 - dh) * 18446744073709551616 + 18446744073709551615) / dh < 2 ^ 64 := Fv256.B.recip_lt dh _ hdh63 hvrel
  refine ⟨_, _, _, ((18446744073709551615 - dh) * 18446744073709551616 + 18446744073709551615) / dh, rfl, hvrel, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp [setRegF]; done)
      | (simp [setRegF, e3, e6, e7, e8, e9, e10] <;> bv_omega)
  · intro k hk
    have hk' : k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3 ∧ k ≠ 4 ∧ k ≠ 5 ∧ k ≠ 6 ∧ k ≠ 11 ∧ k ≠ 12 ∧ k ≠ 13 ∧ k ≠ 15 := by simpa using hk
    obtain ⟨k0, k1, k2, k3, k4, k5, k6, k11, k12, k13, k15⟩ := hk'
    simp [setRegF, k0, k1, k2, k3, k4, k5, k6, k11, k12, k13, k15]
  all_goals first
    | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
       first | (simp only [Nat.reducePow]; rw [Nat.mod_eq_of_lt (by omega)] <;> omega) | (simp only [Nat.reducePow]; exact Nat.mod_eq_of_lt hvB) | skip)
    | janus_frame
  all_goals trace_state

end Fv256.Amd64.KnuthEntry
