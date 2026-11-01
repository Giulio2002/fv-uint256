import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.KnuthMathB
import Fv256.UdivMathB
import Fv256.UdivremMath
import Fv256.Amd64.UdivremA
import Fv256.Amd64.UdivremB
import Fv256.Amd64.UdivremC
import Fv256.Amd64.UdivremD
import Fv256.Amd64.UdivremE
import Fv256.Amd64.UdivremF
import Fv256.Amd64.UdivremG
import Fv256.Amd64.UdivremH

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.UdivremA Fv256.Amd64.UdivremH

namespace Fv256.Amd64.UdivremI

/-- What `udivrem` guarantees on return. -/
def UPost (s0 : State) (M0 : Memory) (sp0 dp qp up remp ra rbpv : Nat) (g : W64) (S' : State) : Prop :=
  ∃ (R' : Nat → W64) (fl' : Flags) (X' : Nat → BitVec 128) (M' : Memory),
    S' = { s0 with regs := R', rip := BitVec.ofNat 64 ra, flags := fl', xmm := X', mem := M' } ∧
    R' 4 = BitVec.ofNat 64 (sp0 + 8) ∧ R' 5 = BitVec.ofNat 64 rbpv ∧ R' 14 = g ∧ X' 15 = s0.xmm 15 ∧
    Fv256.B.wv M' qp 4 = Fv256.B.wv M0 up 4 / Fv256.B.wv M0 dp 4 ∧
    (remp ≠ 0 → Fv256.B.wv M' remp 4 = Fv256.B.wv M0 up 4 % Fv256.B.wv M0 dp 4) ∧
    MemFrame M0 M' [(qp, qp + 32), (remp, remp + 32), (sp0 - 0x148, sp0), (sp0 + 8, sp0 + 0x50)]

theorem sp_arith (sp0 : Nat) (h : 0x150 ≤ sp0) : sp0 - 0xf0 + 0xf8 = sp0 + 8 := by omega

set_option maxHeartbeats 16000000 in
theorem caseL (s0 : State) (R : Nat → W64) (fl : Flags) (M M0 : Memory) (sp0 dp qp qcap ql up remp n ulen s rbpv ra : Nat)
    (F : Front R M M0 sp0 dp qp qcap ql up remp n ulen s rbpv ra) (hlt : ulen < n) (g : W64) (hg : R 14 = g)
    (hsp0 : 0x150 ≤ sp0) (hsp : sp0 + 0x50 ≤ 2 ^ 48) (hMs : M0.accessible (sp0 - 0x148) 0x198 true = true)
    (hup48 : up + 32 ≤ 2 ^ 48) (hua : M0.accessible up 32 false = true) (hdisju : up + 32 ≤ sp0 - 0x148 ∨ sp0 + 0x50 ≤ up)
    (hdp : dp + 32 ≤ 2 ^ 48) (hdisj : dp + 32 ≤ sp0 - 0x148 ∨ sp0 + 0x50 ≤ dp)
    (hq48 : qp + 32 ≤ 2 ^ 48) (hq0 : Fv256.B.wv M0 qp 4 = 0) (hqs : qp + 32 ≤ sp0 - 0x148 ∨ sp0 + 0x50 ≤ qp)
    (hremB : remp < 2 ^ 64)
    (hrem : remp ≠ 0 → remp + 32 ≤ 2 ^ 48 ∧ M0.accessible remp 32 true = true ∧ Fv256.B.wv M0 remp 4 = 0)
    (hqr : remp ≠ 0 → qp + 32 ≤ remp ∨ remp + 32 ≤ qp) (hru : remp ≠ 0 → remp + 32 ≤ up ∨ up + 32 ≤ remp)
    (hrs : remp ≠ 0 → remp + 32 ≤ sp0 - 0x148 ∨ sp0 + 0x50 ≤ remp) (hra47 : ra < 2 ^ 47) (hx15 : s0.xmm 15 = 0) :
    ReachesRet Extracted.program (BitVec.ofNat 64 ra)
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x1a0), flags := fl, mem := M }
      (UPost s0 M0 sp0 dp qp up remp ra rbpv g) := by
  have hcode := ku_lt
  obtain ⟨hn, hn4, hul4, hs63⟩ : 1 ≤ n ∧ n ≤ 4 ∧ ulen ≤ 4 ∧ s ≤ 63 := ⟨F.hn, F.hn4, F.hulen, F.hs⟩
  have hfr := F.frame
  have hUw : Fv256.B.wv M0 up 4 = Fv256.B.wv M up 4 := (Fv256.B.wv_of_frame M0 M _ hfr up 4 (by simp [Outside]; omega)).symm
  have hDw : Fv256.B.wv M0 dp 4 = Fv256.B.wv M dp 4 := (Fv256.B.wv_of_frame M0 M _ hfr dp 4 (by simp [Outside]; omega)).symm
  have hUlt : Fv256.B.wv M0 up 4 < Fv256.B.wv M0 dp 4 := by
    rw [hUw, hDw, F.uwv, F.dwv]
    have h1 := Fv256.B.wv_lt M up ulen
    have h2 := Fv256.B.wv_ge_top M dp n hn
    have h3 : 1 ≤ M.readLE (dp + 8 * (n - 1)) 8 := Nat.pos_of_ne_zero F.dtop
    have h4 : 2 ^ (64 * ulen) ≤ 2 ^ (64 * (n - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    have h5 : 2 ^ (64 * (n - 1)) ≤ M.readLE (dp + 8 * (n - 1)) 8 * 2 ^ (64 * (n - 1)) := Nat.le_mul_of_pos_left _ h3
    omega
  have hqM : Fv256.B.wv M qp 4 = 0 := by
    rw [← hq0]; exact Fv256.B.wv_of_frame M0 M _ hfr qp 4 (by simp [Outside]; omega)
  have hsf : sp0 - 0xf0 + 0xf8 ≤ 2 ^ 48 := by omega
  have hMs' : M.accessible (sp0 - 0xf0) 0xf8 true = true := by
    rw [hfr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hMs (by omega) (by omega)
  have se8 : M.readLE (sp0 - 0xf0 + 0xe8) 8 = rbpv := by rw [show sp0 - 0xf0 + 0xe8 = sp0 - 8 by omega]; exact F.s_e8
  have sf0 : M.readLE (sp0 - 0xf0 + 0xf0) 8 = ra := by rw [show sp0 - 0xf0 + 0xf0 = sp0 by omega]; exact F.s_f0
  by_cases hr0 : remp = 0
  · subst hr0
    have h1 := Fv256.Amd64.UdivremG.ulen_lt_nil s0 n ulen (sp0 - 0xf0) ra rbpv R fl M hn4 hlt hsf (by omega) hMs' F.e12 F.e2
      (by simpa using F.e10) F.e4 se8 sf0 hra47
    refine Fv256.B.reachesRet_mono64 h1 ?_
    rintro S ⟨R', fl', hS, h4, h5, h14⟩
    refine ⟨R', fl', s0.xmm, M, by rw [hS], ?_, h5, ?_, rfl, ?_, ?_, ?_⟩
    · rw [h4, sp_arith sp0 hsp0]
    · rw [h14, hg]
    · rw [hqM, Nat.div_eq_of_lt hUlt]
    · intro h; exact absurd rfl h
    · exact hfr.mono (by intro a n' h; simp [Outside] at h ⊢; omega)
  · obtain ⟨hr48, hra, hr0z⟩ := hrem hr0
    have hua' : M.accessible up 32 false = true := by rw [hfr.accessible]; exact hua
    have hra' : M.accessible remp 32 true = true := by rw [hfr.accessible]; exact hra
    have hMs2 : M.accessible (sp0 - 0xf0 - 0x58) 0x150 true = true := by
      rw [hfr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hMs (by omega) (by omega)
    have h1 := Fv256.Amd64.UdivremG.ulen_lt_ne s0 up remp n ulen (sp0 - 0xf0) ra rbpv R fl M hn4 hlt hr0 hremB hup48 hua' hr48 hra'
      (by have := hru hr0; omega) hsf (by omega) hMs2 (by omega) (by have := hrs hr0; omega) F.e12 F.e2 F.e6 F.e7 F.e10 F.e4 se8 sf0 hra47
    refine Fv256.B.reachesRet_mono64 h1 ?_
    rintro S ⟨R', fl', X', M', hS, h4, h5, hx, h14, hcp, hf'⟩
    refine ⟨R', fl', X', M', by rw [hS], ?_, h5, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h4, sp_arith sp0 hsp0]
    · rw [h14, hg]
    · rw [hx, hx15]
    · have hq' : Fv256.B.wv M' qp 4 = Fv256.B.wv M qp 4 := Fv256.B.wv_of_frame M M' _ hf' qp 4 (by have := hqr hr0; simp [Outside]; omega)
      rw [hq', hqM, Nat.div_eq_of_lt hUlt]
    · intro _
      rw [Nat.mod_eq_of_lt hUlt, hUw]
      exact Fv256.B.wv_congr M' M remp up 4 (fun j hj => hcp j hj)
    · refine hfr.trans hf' ?_
      intro a n' h; simp [Outside] at h ⊢; omega

end Fv256.Amd64.UdivremI
