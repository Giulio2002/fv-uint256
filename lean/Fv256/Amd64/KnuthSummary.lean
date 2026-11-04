import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.KnuthMathB
import Fv256.Amd64.KnuthSub
import Fv256.Amd64.KnuthDefs
import Fv256.Amd64.KnuthLoop
import Fv256.Amd64.KnuthRun
import Fv256.Amd64.KnuthEntry

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.KnuthSub Fv256.Amd64.KnuthDefs

namespace Fv256.Amd64.KnuthSummary

set_option maxHeartbeats 8000000 in
theorem exit_run (s : State) (R2 : Nat → W64) (fl2 : Flags) (M2 : Memory)
    (hR4 : R2 4 = s.regs 4 - 80#64) (hs4 : 80 ≤ (s.regs 4).toNat)
    (hacc : M2.accessible ((s.regs 4).toNat - 80) 0x90 true = true)
    (hrbp : M2.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hret : M2.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8) (hretlt : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    ReachesRet Extracted.program (retAddrOf s) { s with regs := R2, rip := BitVec.ofNat 64 (kn + 0x26b), flags := fl2, mem := M2 }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags), S' = { s with regs := R', rip := retAddrOf s, flags := fl', mem := M2 } ∧
        R' 4 = s.regs 4 + 8 ∧ R' 5 = BitVec.ofNat 64 (s.regs 5).toNat ∧ R' 14 = R2 14) := by
  have hcode := kn_lt
  have hsp : (R2 4).toNat = (s.regs 4).toNat - 80 := by
    rw [hR4, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; have := (s.regs 4).isLt; omega
  have hret2 : M2.readLE ((R2 4).toNat + 80) 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [hsp, show (s.regs 4).toNat - 80 + 80 = (s.regs 4).toNat by omega]; exact hret
  have hrbp2 : M2.readLE ((R2 4).toNat + 72) 8 = (s.regs 5).toNat := by
    rw [hsp, show (s.regs 4).toNat - 80 + 72 = (s.regs 4).toNat - 8 by omega]; exact hrbp
  have hretlt2 : M2.readLE ((R2 4).toNat + 80) 8 < 2 ^ 47 := by rw [hret2]; exact hretlt
  have hacc2 : M2.accessible (R2 4).toNat 0x90 true = true := by rw [hsp]; exact hacc
  janus64_run [hrbp2, hretlt2]
  refine ⟨_, _, rfl, ?_, ?_, ?_⟩
  · simp only [setRegF]; simp; rw [hR4]; bv_omega
  · simp [setRegF]
  · simp [setRegF]
  all_goals trace_state

set_option maxHeartbeats 16000000 in
theorem knuth_summary :
    Summary Extracted.program kn
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        StackGuardOK s 0 ∧ StackWritable s 0x50 0x40 ∧
        2 ≤ (s.regs 10).toNat ∧ (s.regs 10).toNat < 2 ^ 20 ∧ (s.regs 10).toNat ≤ (s.regs 6).toNat ∧ (s.regs 6).toNat < 2 ^ 20 ∧
        (s.regs 6).toNat ≤ (s.regs 8).toNat ∧ (s.regs 8).toNat < 2 ^ 55 ∧
        (s.regs 6).toNat - (s.regs 10).toNat ≤ (s.regs 3).toNat ∧ (s.regs 3).toNat < 2 ^ 20 ∧
        Buffer s (s.regs 7) (8 * (s.regs 6).toNat) true ∧ Buffer s (s.regs 9) (8 * (s.regs 10).toNat) false ∧
        Buffer s (s.regs 0) (8 * (s.regs 3).toNat) true ∧
        ((s.regs 9).toNat + 8 * (s.regs 10).toNat ≤ (s.regs 7).toNat ∨ (s.regs 7).toNat + 8 * (s.regs 6).toNat ≤ (s.regs 9).toNat) ∧
        ((s.regs 0).toNat + 8 * (s.regs 3).toNat ≤ (s.regs 7).toNat ∨ (s.regs 7).toNat + 8 * (s.regs 6).toNat ≤ (s.regs 0).toNat) ∧
        ((s.regs 0).toNat + 8 * (s.regs 3).toNat ≤ (s.regs 9).toNat ∨ (s.regs 9).toNat + 8 * (s.regs 10).toNat ≤ (s.regs 0).toNat) ∧
        ((s.regs 7).toNat + 8 * (s.regs 6).toNat ≤ (s.regs 4).toNat - 0x50 ∨ (s.regs 4).toNat + 0x40 ≤ (s.regs 7).toNat) ∧
        ((s.regs 9).toNat + 8 * (s.regs 10).toNat ≤ (s.regs 4).toNat - 0x50 ∨ (s.regs 4).toNat + 0x40 ≤ (s.regs 9).toNat) ∧
        ((s.regs 0).toNat + 8 * (s.regs 3).toNat ≤ (s.regs 4).toNat - 0x50 ∨ (s.regs 4).toNat + 0x40 ≤ (s.regs 0).toNat) ∧
        2 ^ 63 ≤ s.mem.readLE ((s.regs 9).toNat + 8 * ((s.regs 10).toNat - 1)) 8 ∧
        Fv256.B.wv s.mem ((s.regs 7).toNat + 8 * ((s.regs 6).toNat - (s.regs 10).toNat)) (s.regs 10).toNat <
          Fv256.B.wv s.mem (s.regs 9).toNat (s.regs 10).toNat)
      (fun s s' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        s' = { s with regs := R', rip := retAddrOf s, flags := fl', mem := M' } ∧
        R' 4 = s.regs 4 + 8 ∧ R' 5 = BitVec.ofNat 64 (s.regs 5).toNat ∧ R' 14 = s.regs 14 ∧
        Fv256.B.wv s.mem (s.regs 7).toNat (s.regs 6).toNat =
          Fv256.B.wv s.mem (s.regs 9).toNat (s.regs 10).toNat * Fv256.B.wv M' (s.regs 0).toNat ((s.regs 6).toNat - (s.regs 10).toNat) +
            Fv256.B.wv M' (s.regs 7).toNat (s.regs 10).toNat ∧
        Fv256.B.wv M' (s.regs 7).toNat (s.regs 10).toNat < Fv256.B.wv s.mem (s.regs 9).toNat (s.regs 10).toNat ∧
        MemFrame s.mem M' [((s.regs 7).toNat, (s.regs 7).toNat + 8 * (s.regs 6).toNat),
          ((s.regs 0).toNat, (s.regs 0).toNat + 8 * ((s.regs 6).toNat - (s.regs 10).toNat)),
          ((s.regs 4).toNat - 0x50, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 0x40)]) := by
  intro s hpc ⟨⟨hra1, hra2⟩, hg, hw, hn, hn2, hnm, hm2, hcm, hcapB, hmq, hql2, ⟨hub, hua⟩, ⟨hdb, hda⟩, ⟨hqb, hqa⟩,
    hdu, hqu, hqd, hus, hds, hqs, hdh63, hD⟩
  have hw' := hw
  obtain ⟨hlow, hnw, hacc⟩ := hw'
  simp only [regSP] at hlow hnw hacc
  have hrip : { s with rip := BitVec.ofNat 64 kn } = s := by rw [← hpc]
  have hdh63e : 2 ^ 63 ≤ s.mem.readLE ((s.regs 9).toNat + (s.regs 10).toNat * 8 - 8) 8 := by
    have e : (s.regs 9).toNat + (s.regs 10).toNat * 8 - 8 = (s.regs 9).toNat + 8 * ((s.regs 10).toNat - 1) := by omega
    rw [e]; exact hdh63
  have h1 := Fv256.Amd64.KnuthEntry.knuth_entry s (s.regs 7).toNat (s.regs 9).toNat (s.regs 0).toNat (s.regs 10).toNat
    (s.regs 6).toNat (s.regs 3).toNat (s.regs 8).toNat (s.mem.readLE ((s.regs 9).toNat + (s.regs 10).toNat * 8 - 8) 8)
    (s.mem.readLE ((s.regs 9).toNat + (s.regs 10).toNat * 8 - 16) 8) hg hn hn2 hnm hm2 rfl rfl rfl rfl rfl rfl rfl rfl rfl hdh63e
    hdb hda hw hds
  rw [hrip] at h1
  refine Fv256.B.reachesRet_trans64 h1 ?_
  intro S1 hrip1 ⟨R1, fl1, M1, v, hS1, hv, hHead, hunch, m64, m32, m16, m8, mq16, mq48, mq56, mrbp, hfr1⟩
  subst hS1
  generalize hup : (s.regs 7).toNat = up at *
  generalize hdp : (s.regs 9).toNat = dp at *
  generalize hqp : (s.regs 0).toNat = qp at *
  generalize hn' : (s.regs 10).toNat = n at *
  generalize hm' : (s.regs 6).toNat = m at *
  generalize hql : (s.regs 3).toNat = ql at *
  generalize hcap : (s.regs 8).toNat = cap at *
  generalize hsp0 : (s.regs 4).toNat = sp0 at *
  generalize hdhd : s.mem.readLE (dp + n * 8 - 8) 8 = dh at *
  generalize hdld : s.mem.readLE (dp + n * 8 - 16) 8 = dl at *
  have hsp80 : (s.regs 4 - 80#64).toNat = sp0 - 80 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; have := (s.regs 4).isLt; omega
  have hdhA : dh = M1.readLE (dp + 8 * (n - 1)) 8 := by
    have e1 : s.mem.readLE (dp + 8 * (n - 1)) 8 = dh := by
      rw [show dp + 8 * (n - 1) = dp + n * 8 - 8 by omega]; exact hdhd
    exact ((hfr1.readLE _ _ (by simp [Outside]; omega)).trans e1).symm
  have hdlA : dl = M1.readLE (dp + 8 * (n - 2)) 8 := by
    have e1 : s.mem.readLE (dp + 8 * (n - 2)) 8 = dl := by
      rw [show dp + 8 * (n - 2) = dp + n * 8 - 16 by omega]; exact hdld
    exact ((hfr1.readLE _ _ (by simp [Outside]; omega)).trans e1).symm
  have K : KC up dp qp n m ql v dl dh cap (s.regs 4 - 80#64).toNat M1 := by
    rw [hsp80]
    refine ⟨hn, hn2, hm2, hmq, hql2, hdhA, hdlA, hdh63e, hv, hcm, hcapB, by omega, hub, hdb, hqb, hdu, by omega, by omega, hqu, by omega, hqd,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hfr1.accessible]; exact hua
    · rw [hfr1.accessible]; exact hda
    · rw [hfr1.accessible]; exact hqa
    · rw [hfr1.accessible]; simpa using hacc
    · rw [show sp0 - 80 + 0x10 = sp0 - 64 by omega]; exact m64
    · rw [show sp0 - 80 + 0x30 = sp0 - 32 by omega]; exact m32
    · rw [show sp0 - 80 + 0x40 = sp0 - 16 by omega]; exact m16
    · rw [show sp0 - 80 + 0x58 = sp0 + 8 by omega]; exact m8
    · rw [show sp0 - 80 + 0x60 = sp0 + 16 by omega]; exact mq16
    · rw [show sp0 - 80 + 0x80 = sp0 + 48 by omega]; exact mq48
    · rw [show sp0 - 80 + 0x88 = sp0 + 56 by omega]; exact mq56
  have hI : KInv M1 M1 up dp qp n m (s.regs 4 - 80#64).toNat (m - n) := by
    rw [hsp80]
    refine ⟨?_, ?_, MemFrame.refl _ _⟩
    · rw [show m - (m - n) = n by omega, show m - n - (m - n) = 0 by omega]; simp [Fv256.B.wv]
    · rw [Fv256.B.wv_of_frame s.mem M1 _ hfr1 (up + 8 * (m - n)) n (by simp [Outside]; omega),
        Fv256.B.wv_of_frame s.mem M1 _ hfr1 dp n (by simp [Outside]; omega)]
      exact hD
  have h2 := Fv256.Amd64.KnuthRun.knuth_loop s up dp qp n m ql v dl dh cap M1 (s.regs 4 - 80#64) K (m - n) (Nat.le_refl _) R1 fl1 M1 hHead hI
  refine Fv256.B.reachesRet_trans64 h2 ?_
  intro S2 hrip2 ⟨R2, fl2, M2, hS2, hR2_4, hI2, h14l⟩
  subst hS2
  have hfr2 := hI2.fr
  rw [hsp80] at hfr2
  have hexit := exit_run s R2 fl2 M2 hR2_4 (by omega)
    (by rw [hsp0, hfr2.accessible, hfr1.accessible]; simpa using hacc)
    (by rw [hsp0, hfr2.readLE _ _ (by simp [Outside] <;> omega)]; exact mrbp)
    (by rw [hsp0, hfr2.readLE _ _ (by simp [Outside] <;> omega), hfr1.readLE _ _ (by simp [Outside] <;> omega)])
    (by rw [hsp0]; exact hra2)
  refine Fv256.B.reachesRet_mono64 hexit ?_
  intro S' ⟨R', fl', hS', h4, h5, h14⟩
  subst hS'
  refine ⟨R', fl', M2, rfl, h4, h5, ?_, ?_, ?_, ?_⟩
  · exact h14.trans (h14l.trans (hunch 14 (by simp)))
  · have h0 := hI2.i1
    simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at h0
    rw [Fv256.B.wv_of_frame s.mem M1 _ hfr1 up m (by simp [Outside]; omega),
      Fv256.B.wv_of_frame s.mem M1 _ hfr1 dp n (by simp [Outside]; omega)] at h0
    rw [hup, hdp, hqp, hn', hm']
    exact h0
  · have h0 := hI2.i2
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    rw [Fv256.B.wv_of_frame s.mem M1 _ hfr1 dp n (by simp [Outside]; omega)] at h0
    rw [hup, hdp, hn']
    exact h0
  · rw [hup, hqp, hn', hm', hsp0]
    exact hfr1.trans hfr2 (by intro a n' h; simp [Outside] at h ⊢; omega)

end Fv256.Amd64.KnuthSummary
