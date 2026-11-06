import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecF
import Fv256.Arm64.SegCompose
import Fv256.Arm64.AddModSeg
import Fv256.Arm64.AddModSegB
import Fv256.Arm64.AddModSegZ

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.AddModSeg Fv256.Arm64.AddModSegB Fv256.Arm64.AddModSegZ
open Fv256.Arm64.SegCompose (seg_trans seg_mono)

namespace Fv256.Arm64.AddModComp2

theorem rod_of_data (m : Janus.Arm64.Memory) (hd : Extracted.program.DataLoaded m) :
    m.accessible 1010368 32 false = true := by
  have hne : Extracted.program.data ≠ [] := by decide
  have h := (hd _ (List.head_mem hne)).1
  have hb : (Extracted.program.data.head hne).base = 1010368 := rfl
  have hl : (Extracted.program.data.head hne).bytes.length = 96 := rfl
  rw [hb, hl] at h
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨r, hr, ⟨⟨h1, h2⟩, h3⟩, _⟩ := h
  exact m.accessible_of_mem hr h1 (by omega) h3

/-- the post-condition shared by every generic-path composition -/
def Post (s s' : State) : Prop :=
  s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
  s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
  s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.addmodSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32)
    (s.mem.readLE (s.regs 3).toNat 32) ∧
  MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 856, s.sp.toNat + 16)]

/-- facts after segment A (the prologue and the fast-path test) -/
structure AF (s S1 : State) : Prop where
  r0 : S1.regs 0 = s.regs 0
  r1 : S1.regs 1 = s.regs 1
  r2 : S1.regs 2 = s.regs 2
  r3 : S1.regs 3 = s.regs 3
  r18 : S1.regs 18 = s.regs 18
  r28 : S1.regs 28 = s.regs 28
  r30 : S1.regs 30 = s.regs 30
  r8 : S1.regs 8 = BitVec.ofNat 64 (s.mem.readLE ((s.regs 3).toNat + 24) 8)
  sp1 : S1.sp = s.sp - 368
  hmem : ∀ a n, (a + n ≤ s.sp.toNat - 376 ∨ s.sp.toNat - 360 ≤ a) → S1.mem.readLE a n = s.mem.readLE a n
  hacc : ∀ a n w, S1.mem.accessible a n w = s.mem.accessible a n w
  hx29 : S1.mem.readLE (s.sp.toNat - 376) 8 = (s.regs 29).toNat
  hret : S1.mem.readLE (s.sp.toNat - 368) 8 = (s.regs 30).toNat
  hfr : MemFrame s.mem S1.mem [(s.sp.toNat - 376, s.sp.toNat - 360)]

set_option maxRecDepth 200000 in
theorem AF_of (s S1 : State) (hsb : 856 ≤ s.sp.toNat) (hsc : s.sp.toNat + 16 ≤ 2 ^ 48)
    (q : S1.pc = BitVec.ofNat 64 (Extracted.entry + 0x1c0) ∧ S1.sp = s.sp - 368 ∧
        (∀ i, i ≠ 8 → i ≠ 9 → i ≠ 16 → i ≠ 17 → i ≠ 20 → i ≠ 29 → S1.regs i = s.regs i) ∧
        S1.regs 8 = BitVec.ofNat 64 (s.mem.readLE ((s.regs 3).toNat + 24) 8) ∧ S1.regs 29 = s.sp - 376 ∧
        S1.mem = (s.mem.writeLE (s.sp.toNat - 376) 8 (s.regs 29).toNat).writeLE (s.sp.toNat - 368) 8 (s.regs 30).toNat) :
    AF s S1 := by
  obtain ⟨q1pc, q1sp, q1r, q18, q129, q1mem⟩ := q
  refine ⟨q1r 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    q1r 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    q1r 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    q1r 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    q1r 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    q1r 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    q1r 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), q18, q1sp, ?_, ?_, ?_, ?_, ?_⟩
  · intro a n h
    rw [q1mem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  · intro a n w; rw [q1mem]; simp
  · rw [q1mem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (s.regs 29).isLt; simpa using this)
  · rw [q1mem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (s.regs 30).isLt; simpa using this)
  · rw [q1mem]
    exact ((MemFrame.refl s.mem _).writeLE _ (r := (s.sp.toNat - 376, s.sp.toNat - 360)) (by simp) (by dsimp only; omega)
      (by dsimp only; omega)).writeLE _ (r := (s.sp.toNat - 376, s.sp.toNat - 360)) (by simp) (by dsimp only; omega)
      (by dsimp only; omega)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem gb_nov (s : State) (hpc : s.pc = BitVec.ofNat 64 Extracted.entry)
    (hpre : Fv256.Arm64.AddModSeg.PreS s) (hnc : ¬ (s.mem.readLE ((s.regs 3).toNat + 24) 8 ≠ 0 ∧ s.mem.readLE ((s.regs 1).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8 ∧ s.mem.readLE ((s.regs 2).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8))
    (hne : s.regs 3 ≠ s.regs 0)
    (hm : ¬ (s.mem.readLE (s.regs 3).toNat 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 8) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 16) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0))
    (hnov : s.mem.readLE (s.regs 1).toNat 32 + s.mem.readLE (s.regs 2).toNat 32 < 2 ^ 256) :
    ReachesRet Extracted.program (s.regs 30) s (Post s) := by
  obtain ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hdata, hgw, hzb, hza, hxb, hxa, hyb, hya, hmb, hma, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩ := hpre
  have hzm' := (hzm.resolve_left (fun h => hne h.symm))
  have hrod := rod_of_data _ hdata
  have hm32 : s.mem.readLE (s.regs 3).toNat 32 ≠ 0 := by
    intro h
    apply hm
    have b0 := Util.readLE8_lt s.mem (s.regs 3).toNat
    have b1 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 8)
    have b2 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 16)
    have b3 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 24)
    rw [Util.readLE_32] at h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  refine seg_trans (segA s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hdata, hgw, hzb, hza, hxb, hxa, hyb, hya, hmb, hma, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩ hnc) ?_
  intro S1 h1pc q1
  obtain ⟨r0, r1, r2, r3, r18, r28, r30, r8, sp1, hmem1, hacc1, hx29, hretS, hfr1⟩ := AF_of s S1 hsb hsc q1
  have sp1n : S1.sp.toNat = s.sp.toNat - 368 := by rw [sp1]; simp [BitVec.toNat_sub]; omega
  refine seg_trans (segB S1 h1pc ?_ ?_ ?_ ?_ ?_) ?_
  · rw [r3, hmem1 _ _ (by omega), hmem1 (_ + 8) _ (by omega), hmem1 (_ + 16) _ (by omega), hmem1 (_ + 24) _ (by omega)]
    exact hm
  · rw [r3, r0]; exact hne
  · rw [r3]; exact hmb
  · rw [r3, hacc1]; exact hma
  · rw [r8, r3, hmem1 _ _ (by omega)]
  intro S2 h2pc ⟨q2pc, q2mem, q2sp, q28, q2r⟩
  have t8 : S2.regs 8 = s.regs 3 := by rw [q28, r3]
  have t8n : (S2.regs 8).toNat = (s.regs 3).toNat := by rw [t8]
  have hmem2 : ∀ a n, (a + n ≤ s.sp.toNat - 376 ∨ s.sp.toNat - 360 ≤ a) → S2.mem.readLE a n = s.mem.readLE a n := by
    intro a n h; rw [q2mem]; exact hmem1 a n h
  have hacc2 : ∀ a n w, S2.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [q2mem]; exact hacc1 a n w
  have hx29_2 : S2.mem.readLE (s.sp.toNat - 376) 8 = (s.regs 29).toNat := by rw [q2mem]; exact hx29
  have hret_2 : S2.mem.readLE (s.sp.toNat - 368) 8 = (s.regs 30).toNat := by rw [q2mem]; exact hretS
  have f2 : MemFrame s.mem S2.mem [(s.sp.toNat - 376, s.sp.toNat - 360)] := by rw [q2mem]; exact hfr1
  have t0 : S2.regs 0 = s.regs 0 := by rw [q2r 0 (by decide) (by decide) (by decide), r0]
  have t1 : S2.regs 1 = s.regs 1 := by rw [q2r 1 (by decide) (by decide) (by decide), r1]
  have t2 : S2.regs 2 = s.regs 2 := by rw [q2r 2 (by decide) (by decide) (by decide), r2]
  have t3 : S2.regs 3 = s.regs 3 := by rw [q2r 3 (by decide) (by decide) (by decide), r3]
  have t18 : S2.regs 18 = s.regs 18 := by rw [q2r 18 (by decide) (by decide) (by decide), r18]
  have t28 : S2.regs 28 = s.regs 28 := by rw [q2r 28 (by decide) (by decide) (by decide), r28]
  have t30 : S2.regs 30 = s.regs 30 := by rw [q2r 30 (by decide) (by decide) (by decide), r30]
  have sp2 : S2.sp = s.sp - 368 := by rw [q2sp, sp1]
  have sp2n : S2.sp.toNat = s.sp.toNat - 368 := by rw [sp2]; simp [BitVec.toNat_sub]; omega
  refine seg_trans (segC S2 h2pc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · rw [t0]; exact hzb
  · rw [t0, hacc2]; exact hza
  · rw [t1]; exact hxb
  · rw [t1, hacc2]; exact hxa
  · rw [t2]; exact hyb
  · rw [t2, hacc2]; exact hya
  · rw [t0, t1]; exact hzx
  · rw [t0, t2]; exact hzy
  · rw [t1, t2, hmem2 _ _ (by omega), hmem2 _ _ (by omega)]; exact hnov
  intro S3 h3pc ⟨q3pc, q3sp, q3r, q3frame, q3val⟩
  have sp3 : S3.sp = s.sp - 368 := by rw [q3sp, sp2]
  have sp3n : S3.sp.toNat = s.sp.toNat - 368 := by rw [sp3]; simp [BitVec.toNat_sub]; omega
  have u0 : S3.regs 0 = s.regs 0 := by rw [q3r 0 (by decide) (by decide), t0]
  have u8 : (S3.regs 8).toNat = (S2.regs 8).toNat := by rw [q3r 8 (by decide) (by decide)]
  have u18 : S3.regs 18 = s.regs 18 := by rw [q3r 18 (by decide) (by decide), t18]
  have u28 : S3.regs 28 = s.regs 28 := by rw [q3r 28 (by decide) (by decide), t28]
  have hmem3 : ∀ a n, ((a + n ≤ (s.regs 0).toNat ∨ (s.regs 0).toNat + 32 ≤ a)) → S3.mem.readLE a n = S2.mem.readLE a n := by
    intro a n h
    apply q3frame.readLE
    simp only [Outside, and_true]; rw [t0]; exact h
  have hacc3 : ∀ a n w, S3.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [q3frame.accessible, hacc2]
  have hx29_3 : S3.mem.readLE (S3.sp.toNat - 8) 8 = (s.regs 29).toNat := by
    rw [sp3n, hmem3 _ _ (by omega)]
    have e : s.sp.toNat - 368 - 8 = s.sp.toNat - 376 := by omega
    rw [e]; exact hx29_2
  have hret_3 : S3.mem.readLE S3.sp.toNat 8 = (s.regs 30).toNat := by
    rw [sp3n, hmem3 _ _ (by omega)]; exact hret_2
  have mptr : (S3.regs 8).toNat = (s.regs 3).toNat := by rw [u8, t8n]
  have mval : S3.mem.readLE (S3.regs 8).toNat 32 = s.mem.readLE (s.regs 3).toNat 32 := by
    rw [mptr, hmem3 _ _ (by omega), hmem2 _ _ (by omega)]
  have vz : S3.mem.readLE (s.regs 0).toNat 32 = s.mem.readLE (s.regs 1).toNat 32 + s.mem.readLE (s.regs 2).toNat 32 := by
    have := q3val
    rw [t0, t1, t2] at this
    rw [this, hmem2 _ _ (by omega), hmem2 _ _ (by omega)]
  have f3 : MemFrame s.mem S3.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 856, s.sp.toNat + 16)] := by
    rw [t0] at q3frame
    exact f2.trans q3frame (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)
  refine seg_mono (segD S3 (s.regs 30) (s.regs 29) h3pc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · rw [hacc3]; exact s.mem.accessible_mono hsw (by omega) (by omega)
  · rw [u28]; exact hg1
  · rw [u28, hacc3]; exact hg2
  · rw [u28, hmem3 ((s.regs 28).toNat + 16) 8 (by omega), hmem2 ((s.regs 28).toNat + 16) 8 (by omega)]; omega
  · rw [u28]; omega
  · rw [u0]; exact hzb
  · rw [u0, hacc3]; exact hza
  · rw [mptr]; exact hmb
  · rw [hacc3, mptr]; exact hma
  · rw [u0]; omega
  · rw [mptr]; omega
  · exact hret_3
  · exact h30a
  · exact h30b
  · exact hx29_3
  intro S4 ⟨q4pc, q4sp, q40, q428, q429, q418, q430, q4val, q4frame⟩
  refine ⟨q4pc, ?_, ?_, ?_, ?_, q429, q430, ?_, ?_⟩
  · rw [q4sp, sp3]; exact BitVec.sub_add_cancel _ _
  · rw [q40, u0]
  · rw [q418, u18]
  · rw [q428, u28]
  · rw [u0, mval, vz] at q4val
    rw [q4val]
    simp [Fv256.F.addmodSpec, Fv256.B.modSpec]
  · rw [u0, sp3n] at q4frame
    exact f3.trans q4frame (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem gb_ov (s : State) (hpc : s.pc = BitVec.ofNat 64 Extracted.entry)
    (hpre : Fv256.Arm64.AddModSeg.PreS s) (hnc : ¬ (s.mem.readLE ((s.regs 3).toNat + 24) 8 ≠ 0 ∧ s.mem.readLE ((s.regs 1).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8 ∧ s.mem.readLE ((s.regs 2).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8))
    (hne : s.regs 3 ≠ s.regs 0)
    (hm : ¬ (s.mem.readLE (s.regs 3).toNat 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 8) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 16) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0))
    (hov : 2 ^ 256 ≤ s.mem.readLE (s.regs 1).toNat 32 + s.mem.readLE (s.regs 2).toNat 32) :
    ReachesRet Extracted.program (s.regs 30) s (Post s) := by
  obtain ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hdata, hgw, hzb, hza, hxb, hxa, hyb, hya, hmb, hma, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩ := hpre
  have hzm' := (hzm.resolve_left (fun h => hne h.symm))
  have hrod := rod_of_data _ hdata
  have hm32 : s.mem.readLE (s.regs 3).toNat 32 ≠ 0 := by
    intro h
    apply hm
    have b0 := Util.readLE8_lt s.mem (s.regs 3).toNat
    have b1 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 8)
    have b2 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 16)
    have b3 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 24)
    rw [Util.readLE_32] at h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  refine seg_trans (segA s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hdata, hgw, hzb, hza, hxb, hxa, hyb, hya, hmb, hma, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩ hnc) ?_
  intro S1 h1pc q1
  obtain ⟨r0, r1, r2, r3, r18, r28, r30, r8, sp1, hmem1, hacc1, hx29, hretS, hfr1⟩ := AF_of s S1 hsb hsc q1
  have sp1n : S1.sp.toNat = s.sp.toNat - 368 := by rw [sp1]; simp [BitVec.toNat_sub]; omega
  refine seg_trans (segB S1 h1pc ?_ ?_ ?_ ?_ ?_) ?_
  · rw [r3, hmem1 _ _ (by omega), hmem1 (_ + 8) _ (by omega), hmem1 (_ + 16) _ (by omega), hmem1 (_ + 24) _ (by omega)]
    exact hm
  · rw [r3, r0]; exact hne
  · rw [r3]; exact hmb
  · rw [r3, hacc1]; exact hma
  · rw [r8, r3, hmem1 _ _ (by omega)]
  intro S2 h2pc ⟨q2pc, q2mem, q2sp, q28, q2r⟩
  have t8 : S2.regs 8 = s.regs 3 := by rw [q28, r3]
  have t8n : (S2.regs 8).toNat = (s.regs 3).toNat := by rw [t8]
  have hmem2 : ∀ a n, (a + n ≤ s.sp.toNat - 376 ∨ s.sp.toNat - 360 ≤ a) → S2.mem.readLE a n = s.mem.readLE a n := by
    intro a n h; rw [q2mem]; exact hmem1 a n h
  have hacc2 : ∀ a n w, S2.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [q2mem]; exact hacc1 a n w
  have hx29_2 : S2.mem.readLE (s.sp.toNat - 376) 8 = (s.regs 29).toNat := by rw [q2mem]; exact hx29
  have hret_2 : S2.mem.readLE (s.sp.toNat - 368) 8 = (s.regs 30).toNat := by rw [q2mem]; exact hretS
  have f2 : MemFrame s.mem S2.mem [(s.sp.toNat - 376, s.sp.toNat - 360)] := by rw [q2mem]; exact hfr1
  have t0 : S2.regs 0 = s.regs 0 := by rw [q2r 0 (by decide) (by decide) (by decide), r0]
  have t1 : S2.regs 1 = s.regs 1 := by rw [q2r 1 (by decide) (by decide) (by decide), r1]
  have t2 : S2.regs 2 = s.regs 2 := by rw [q2r 2 (by decide) (by decide) (by decide), r2]
  have t3 : S2.regs 3 = s.regs 3 := by rw [q2r 3 (by decide) (by decide) (by decide), r3]
  have t18 : S2.regs 18 = s.regs 18 := by rw [q2r 18 (by decide) (by decide) (by decide), r18]
  have t28 : S2.regs 28 = s.regs 28 := by rw [q2r 28 (by decide) (by decide) (by decide), r28]
  have t30 : S2.regs 30 = s.regs 30 := by rw [q2r 30 (by decide) (by decide) (by decide), r30]
  have sp2 : S2.sp = s.sp - 368 := by rw [q2sp, sp1]
  have sp2n : S2.sp.toNat = s.sp.toNat - 368 := by rw [sp2]; simp [BitVec.toNat_sub]; omega
  refine seg_trans (segCov S2 h2pc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · rw [t0]; exact hzb
  · rw [t0, hacc2]; exact hza
  · rw [t1]; exact hxb
  · rw [t1, hacc2]; exact hxa
  · rw [t2]; exact hyb
  · rw [t2, hacc2]; exact hya
  · rw [t0, t1]; exact hzx
  · rw [t0, t2]; exact hzy
  · rw [t1, t2, hmem2 _ _ (by omega), hmem2 _ _ (by omega)]; exact hov
  intro S3 h3pc ⟨q3pc, q3sp, q3r, q3frame, q3val⟩
  have sp3 : S3.sp = s.sp - 368 := by rw [q3sp, sp2]
  have sp3n : S3.sp.toNat = s.sp.toNat - 368 := by rw [sp3]; simp [BitVec.toNat_sub]; omega
  have u0 : S3.regs 0 = s.regs 0 := by rw [q3r 0 (by decide) (by decide), t0]
  have u8 : (S3.regs 8).toNat = (S2.regs 8).toNat := by rw [q3r 8 (by decide) (by decide)]
  have u18 : S3.regs 18 = s.regs 18 := by rw [q3r 18 (by decide) (by decide), t18]
  have u28 : S3.regs 28 = s.regs 28 := by rw [q3r 28 (by decide) (by decide), t28]
  have hmem3 : ∀ a n, ((a + n ≤ (s.regs 0).toNat ∨ (s.regs 0).toNat + 32 ≤ a)) → S3.mem.readLE a n = S2.mem.readLE a n := by
    intro a n h
    apply q3frame.readLE
    simp only [Outside, and_true]; rw [t0]; exact h
  have hacc3 : ∀ a n w, S3.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [q3frame.accessible, hacc2]
  have hx29_3 : S3.mem.readLE (S3.sp.toNat - 8) 8 = (s.regs 29).toNat := by
    rw [sp3n, hmem3 _ _ (by omega)]
    have e : s.sp.toNat - 368 - 8 = s.sp.toNat - 376 := by omega
    rw [e]; exact hx29_2
  have hret_3 : S3.mem.readLE S3.sp.toNat 8 = (s.regs 30).toNat := by
    rw [sp3n, hmem3 _ _ (by omega)]; exact hret_2
  have mptr : (S3.regs 8).toNat = (s.regs 3).toNat := by rw [u8, t8n]
  have mval : S3.mem.readLE (S3.regs 8).toNat 32 = s.mem.readLE (s.regs 3).toNat 32 := by
    rw [mptr, hmem3 _ _ (by omega), hmem2 _ _ (by omega)]
  have vz : S3.mem.readLE (s.regs 0).toNat 32 + 2 ^ 256 = s.mem.readLE (s.regs 1).toNat 32 + s.mem.readLE (s.regs 2).toNat 32 := by
    have := q3val
    rw [t0, t1, t2] at this
    rw [this, hmem2 _ _ (by omega), hmem2 _ _ (by omega)]
  have f3 : MemFrame s.mem S3.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 856, s.sp.toNat + 16)] := by
    rw [t0] at q3frame
    exact f2.trans q3frame (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)
  refine seg_mono (segEF S3 (s.regs 30) (s.regs 29) h3pc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · rw [hacc3]; exact s.mem.accessible_mono hsw (by omega) (by omega)
  · rw [hacc3]; exact hrod
  · rw [u28]; exact hg1
  · rw [u28, hacc3]; exact hg2
  · rw [u28, hmem3 ((s.regs 28).toNat + 16) 8 (by omega), hmem2 ((s.regs 28).toNat + 16) 8 (by omega)]; omega
  · rw [u28, sp3n]; omega
  · rw [u0]; exact hzb
  · rw [u0, hacc3]; exact hza
  · rw [mptr]; exact hmb
  · rw [hacc3, mptr]; exact hma
  · rw [u0, sp3n]; omega
  · rw [mptr, sp3n]; omega
  · rw [mptr, u0]; omega
  · rw [mval]; exact hm32
  · exact hret_3
  · exact h30a
  · exact h30b
  · exact hx29_3
  intro S4 ⟨q4pc, q4sp, q40, q428, q429, q418, q430, q4val, q4frame⟩
  refine ⟨q4pc, ?_, ?_, ?_, ?_, q429, q430, ?_, ?_⟩
  · rw [q4sp, sp3]; exact BitVec.sub_add_cancel _ _
  · rw [q40, u0]
  · rw [q418, u18]
  · rw [q428, u28]
  · rw [u0, mval, vz] at q4val
    rw [q4val]
    simp [Fv256.F.addmodSpec, hm32]
  · rw [u0, sp3n] at q4frame
    exact f3.trans q4frame (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem ga_nov (s : State) (hpc : s.pc = BitVec.ofNat 64 Extracted.entry)
    (hpre : Fv256.Arm64.AddModSeg.PreS s) (hnc : ¬ (s.mem.readLE ((s.regs 3).toNat + 24) 8 ≠ 0 ∧ s.mem.readLE ((s.regs 1).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8 ∧ s.mem.readLE ((s.regs 2).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8))
    (hzeq : s.regs 3 = s.regs 0)
    (hm : ¬ (s.mem.readLE (s.regs 3).toNat 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 8) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 16) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0))
    (hnov : s.mem.readLE (s.regs 1).toNat 32 + s.mem.readLE (s.regs 2).toNat 32 < 2 ^ 256) :
    ReachesRet Extracted.program (s.regs 30) s (Post s) := by
  obtain ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hdata, hgw, hzb, hza, hxb, hxa, hyb, hya, hmb, hma, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩ := hpre
  have hrod := rod_of_data _ hdata
  have hm32 : s.mem.readLE (s.regs 3).toNat 32 ≠ 0 := by
    intro h
    apply hm
    have b0 := Util.readLE8_lt s.mem (s.regs 3).toNat
    have b1 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 8)
    have b2 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 16)
    have b3 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 24)
    rw [Util.readLE_32] at h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  refine seg_trans (segA s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hdata, hgw, hzb, hza, hxb, hxa, hyb, hya, hmb, hma, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩ hnc) ?_
  intro S1 h1pc q1
  obtain ⟨r0, r1, r2, r3, r18, r28, r30, r8, sp1, hmem1, hacc1, hx29, hretS, hfr1⟩ := AF_of s S1 hsb hsc q1
  have sp1n : S1.sp.toNat = s.sp.toNat - 368 := by rw [sp1]; simp [BitVec.toNat_sub]; omega
  refine seg_trans (segBc S1 h1pc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · rw [r3, hmem1 _ _ (by omega), hmem1 (_ + 8) _ (by omega), hmem1 (_ + 16) _ (by omega), hmem1 (_ + 24) _ (by omega)]
    exact hm
  · rw [r3, r0]; exact hzeq
  · rw [r3]; exact hmb
  · rw [r3, hacc1]; exact hma
  · omega
  · omega
  · rw [hacc1, sp1n]; exact s.mem.accessible_mono hsw (by omega) (by omega)
  · rw [r3, sp1n]; omega
  · rw [r8, r3, hmem1 _ _ (by omega)]
  intro S2 h2pc ⟨q2pc, q2sp, q2r8, q2r, q2fr, q2val⟩
  have t8n : (S2.regs 8).toNat = s.sp.toNat - 40 := by rw [q2r8]; simp [BitVec.toNat_add]; omega
  rw [sp1n] at q2fr q2val
  have hmem2 : ∀ a n, (a + n ≤ s.sp.toNat - 376 ∨ s.sp.toNat - 360 ≤ a) → (a + n ≤ s.sp.toNat - 40 ∨ s.sp.toNat - 8 ≤ a) →
      S2.mem.readLE a n = s.mem.readLE a n := by
    intro a n h h'
    rw [q2fr.readLE a n (by simp only [Outside, and_true]; omega), hmem1 a n h]
  have hacc2 : ∀ a n w, S2.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [q2fr.accessible, hacc1]
  have hx29_2 : S2.mem.readLE (s.sp.toNat - 376) 8 = (s.regs 29).toNat := by
    rw [q2fr.readLE _ _ (by simp only [Outside, and_true]; omega)]; exact hx29
  have hret_2 : S2.mem.readLE (s.sp.toNat - 368) 8 = (s.regs 30).toNat := by
    rw [q2fr.readLE _ _ (by simp only [Outside, and_true]; omega)]; exact hretS
  have f2 : MemFrame s.mem S2.mem [(s.sp.toNat - 376, s.sp.toNat - 360), (s.sp.toNat - 40, s.sp.toNat - 8)] :=
    hfr1.trans q2fr (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)
  have hclone : S2.mem.readLE (s.sp.toNat - 40) 32 = s.mem.readLE (s.regs 3).toNat 32 := by
    have e : S1.mem.readLE (S1.regs 3).toNat 32 = s.mem.readLE (s.regs 3).toNat 32 := by
      rw [r3]; exact hmem1 _ _ (by omega)
    have := q2val
    rw [e] at this
    have e2 : s.sp.toNat - 368 + 328 = s.sp.toNat - 40 := by omega
    rw [e2] at this
    exact this
  have t0 : S2.regs 0 = s.regs 0 := by rw [q2r 0 (by decide) (by decide) (by decide), r0]
  have t1 : S2.regs 1 = s.regs 1 := by rw [q2r 1 (by decide) (by decide) (by decide), r1]
  have t2 : S2.regs 2 = s.regs 2 := by rw [q2r 2 (by decide) (by decide) (by decide), r2]
  have t3 : S2.regs 3 = s.regs 3 := by rw [q2r 3 (by decide) (by decide) (by decide), r3]
  have t18 : S2.regs 18 = s.regs 18 := by rw [q2r 18 (by decide) (by decide) (by decide), r18]
  have t28 : S2.regs 28 = s.regs 28 := by rw [q2r 28 (by decide) (by decide) (by decide), r28]
  have t30 : S2.regs 30 = s.regs 30 := by rw [q2r 30 (by decide) (by decide) (by decide), r30]
  have sp2 : S2.sp = s.sp - 368 := by rw [q2sp, sp1]
  have sp2n : S2.sp.toNat = s.sp.toNat - 368 := by rw [sp2]; simp [BitVec.toNat_sub]; omega
  refine seg_trans (segC S2 h2pc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · rw [t0]; exact hzb
  · rw [t0, hacc2]; exact hza
  · rw [t1]; exact hxb
  · rw [t1, hacc2]; exact hxa
  · rw [t2]; exact hyb
  · rw [t2, hacc2]; exact hya
  · rw [t0, t1]; exact hzx
  · rw [t0, t2]; exact hzy
  · rw [t1, t2, hmem2 _ _ (by omega) (by omega), hmem2 _ _ (by omega) (by omega)]; exact hnov
  intro S3 h3pc ⟨q3pc, q3sp, q3r, q3frame, q3val⟩
  have sp3 : S3.sp = s.sp - 368 := by rw [q3sp, sp2]
  have sp3n : S3.sp.toNat = s.sp.toNat - 368 := by rw [sp3]; simp [BitVec.toNat_sub]; omega
  have u0 : S3.regs 0 = s.regs 0 := by rw [q3r 0 (by decide) (by decide), t0]
  have u8 : (S3.regs 8).toNat = (S2.regs 8).toNat := by rw [q3r 8 (by decide) (by decide)]
  have u18 : S3.regs 18 = s.regs 18 := by rw [q3r 18 (by decide) (by decide), t18]
  have u28 : S3.regs 28 = s.regs 28 := by rw [q3r 28 (by decide) (by decide), t28]
  have hmem3 : ∀ a n, ((a + n ≤ (s.regs 0).toNat ∨ (s.regs 0).toNat + 32 ≤ a)) → S3.mem.readLE a n = S2.mem.readLE a n := by
    intro a n h
    apply q3frame.readLE
    simp only [Outside, and_true]; rw [t0]; exact h
  have hacc3 : ∀ a n w, S3.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [q3frame.accessible, hacc2]
  have hx29_3 : S3.mem.readLE (S3.sp.toNat - 8) 8 = (s.regs 29).toNat := by
    rw [sp3n, hmem3 _ _ (by omega)]
    have e : s.sp.toNat - 368 - 8 = s.sp.toNat - 376 := by omega
    rw [e]; exact hx29_2
  have hret_3 : S3.mem.readLE S3.sp.toNat 8 = (s.regs 30).toNat := by
    rw [sp3n, hmem3 _ _ (by omega)]; exact hret_2
  have mptr : (S3.regs 8).toNat = s.sp.toNat - 40 := by rw [u8, t8n]
  have mval : S3.mem.readLE (S3.regs 8).toNat 32 = s.mem.readLE (s.regs 3).toNat 32 := by
    rw [mptr, hmem3 _ _ (by omega)]; exact hclone
  have vz : S3.mem.readLE (s.regs 0).toNat 32 = s.mem.readLE (s.regs 1).toNat 32 + s.mem.readLE (s.regs 2).toNat 32 := by
    have := q3val
    rw [t0, t1, t2] at this
    rw [this, hmem2 _ _ (by omega) (by omega), hmem2 _ _ (by omega) (by omega)]
  have f3 : MemFrame s.mem S3.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 856, s.sp.toNat + 16)] := by
    rw [t0] at q3frame
    exact f2.trans q3frame (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)
  refine seg_mono (segD S3 (s.regs 30) (s.regs 29) h3pc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · rw [hacc3]; exact s.mem.accessible_mono hsw (by omega) (by omega)
  · rw [u28]; exact hg1
  · rw [u28, hacc3]; exact hg2
  · rw [u28, hmem3 ((s.regs 28).toNat + 16) 8 (by omega), hmem2 ((s.regs 28).toNat + 16) 8 (by omega) (by omega)]; omega
  · rw [u28]; omega
  · rw [u0]; exact hzb
  · rw [u0, hacc3]; exact hza
  · rw [mptr]; omega
  · rw [hacc3, mptr]; exact s.mem.accessible_sub hsw (Or.inl rfl) (by omega) (by omega)
  · rw [u0]; omega
  · rw [mptr]; omega
  · exact hret_3
  · exact h30a
  · exact h30b
  · exact hx29_3
  intro S4 ⟨q4pc, q4sp, q40, q428, q429, q418, q430, q4val, q4frame⟩
  refine ⟨q4pc, ?_, ?_, ?_, ?_, q429, q430, ?_, ?_⟩
  · rw [q4sp, sp3]; exact BitVec.sub_add_cancel _ _
  · rw [q40, u0]
  · rw [q418, u18]
  · rw [q428, u28]
  · rw [u0, mval, vz] at q4val
    rw [q4val]
    simp [Fv256.F.addmodSpec, Fv256.B.modSpec]
  · rw [u0, sp3n] at q4frame
    exact f3.trans q4frame (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem ga_ov (s : State) (hpc : s.pc = BitVec.ofNat 64 Extracted.entry)
    (hpre : Fv256.Arm64.AddModSeg.PreS s) (hnc : ¬ (s.mem.readLE ((s.regs 3).toNat + 24) 8 ≠ 0 ∧ s.mem.readLE ((s.regs 1).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8 ∧ s.mem.readLE ((s.regs 2).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8))
    (hzeq : s.regs 3 = s.regs 0)
    (hm : ¬ (s.mem.readLE (s.regs 3).toNat 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 8) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 16) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0))
    (hov : 2 ^ 256 ≤ s.mem.readLE (s.regs 1).toNat 32 + s.mem.readLE (s.regs 2).toNat 32) :
    ReachesRet Extracted.program (s.regs 30) s (Post s) := by
  obtain ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hdata, hgw, hzb, hza, hxb, hxa, hyb, hya, hmb, hma, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩ := hpre
  have hrod := rod_of_data _ hdata
  have hm32 : s.mem.readLE (s.regs 3).toNat 32 ≠ 0 := by
    intro h
    apply hm
    have b0 := Util.readLE8_lt s.mem (s.regs 3).toNat
    have b1 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 8)
    have b2 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 16)
    have b3 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 24)
    rw [Util.readLE_32] at h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  refine seg_trans (segA s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hdata, hgw, hzb, hza, hxb, hxa, hyb, hya, hmb, hma, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩ hnc) ?_
  intro S1 h1pc q1
  obtain ⟨r0, r1, r2, r3, r18, r28, r30, r8, sp1, hmem1, hacc1, hx29, hretS, hfr1⟩ := AF_of s S1 hsb hsc q1
  have sp1n : S1.sp.toNat = s.sp.toNat - 368 := by rw [sp1]; simp [BitVec.toNat_sub]; omega
  refine seg_trans (segBc S1 h1pc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · rw [r3, hmem1 _ _ (by omega), hmem1 (_ + 8) _ (by omega), hmem1 (_ + 16) _ (by omega), hmem1 (_ + 24) _ (by omega)]
    exact hm
  · rw [r3, r0]; exact hzeq
  · rw [r3]; exact hmb
  · rw [r3, hacc1]; exact hma
  · omega
  · omega
  · rw [hacc1, sp1n]; exact s.mem.accessible_mono hsw (by omega) (by omega)
  · rw [r3, sp1n]; omega
  · rw [r8, r3, hmem1 _ _ (by omega)]
  intro S2 h2pc ⟨q2pc, q2sp, q2r8, q2r, q2fr, q2val⟩
  have t8n : (S2.regs 8).toNat = s.sp.toNat - 40 := by rw [q2r8]; simp [BitVec.toNat_add]; omega
  rw [sp1n] at q2fr q2val
  have hmem2 : ∀ a n, (a + n ≤ s.sp.toNat - 376 ∨ s.sp.toNat - 360 ≤ a) → (a + n ≤ s.sp.toNat - 40 ∨ s.sp.toNat - 8 ≤ a) →
      S2.mem.readLE a n = s.mem.readLE a n := by
    intro a n h h'
    rw [q2fr.readLE a n (by simp only [Outside, and_true]; omega), hmem1 a n h]
  have hacc2 : ∀ a n w, S2.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [q2fr.accessible, hacc1]
  have hx29_2 : S2.mem.readLE (s.sp.toNat - 376) 8 = (s.regs 29).toNat := by
    rw [q2fr.readLE _ _ (by simp only [Outside, and_true]; omega)]; exact hx29
  have hret_2 : S2.mem.readLE (s.sp.toNat - 368) 8 = (s.regs 30).toNat := by
    rw [q2fr.readLE _ _ (by simp only [Outside, and_true]; omega)]; exact hretS
  have f2 : MemFrame s.mem S2.mem [(s.sp.toNat - 376, s.sp.toNat - 360), (s.sp.toNat - 40, s.sp.toNat - 8)] :=
    hfr1.trans q2fr (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)
  have hclone : S2.mem.readLE (s.sp.toNat - 40) 32 = s.mem.readLE (s.regs 3).toNat 32 := by
    have e : S1.mem.readLE (S1.regs 3).toNat 32 = s.mem.readLE (s.regs 3).toNat 32 := by
      rw [r3]; exact hmem1 _ _ (by omega)
    have := q2val
    rw [e] at this
    have e2 : s.sp.toNat - 368 + 328 = s.sp.toNat - 40 := by omega
    rw [e2] at this
    exact this
  have t0 : S2.regs 0 = s.regs 0 := by rw [q2r 0 (by decide) (by decide) (by decide), r0]
  have t1 : S2.regs 1 = s.regs 1 := by rw [q2r 1 (by decide) (by decide) (by decide), r1]
  have t2 : S2.regs 2 = s.regs 2 := by rw [q2r 2 (by decide) (by decide) (by decide), r2]
  have t3 : S2.regs 3 = s.regs 3 := by rw [q2r 3 (by decide) (by decide) (by decide), r3]
  have t18 : S2.regs 18 = s.regs 18 := by rw [q2r 18 (by decide) (by decide) (by decide), r18]
  have t28 : S2.regs 28 = s.regs 28 := by rw [q2r 28 (by decide) (by decide) (by decide), r28]
  have t30 : S2.regs 30 = s.regs 30 := by rw [q2r 30 (by decide) (by decide) (by decide), r30]
  have sp2 : S2.sp = s.sp - 368 := by rw [q2sp, sp1]
  have sp2n : S2.sp.toNat = s.sp.toNat - 368 := by rw [sp2]; simp [BitVec.toNat_sub]; omega
  refine seg_trans (segCov S2 h2pc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · rw [t0]; exact hzb
  · rw [t0, hacc2]; exact hza
  · rw [t1]; exact hxb
  · rw [t1, hacc2]; exact hxa
  · rw [t2]; exact hyb
  · rw [t2, hacc2]; exact hya
  · rw [t0, t1]; exact hzx
  · rw [t0, t2]; exact hzy
  · rw [t1, t2, hmem2 _ _ (by omega) (by omega), hmem2 _ _ (by omega) (by omega)]; exact hov
  intro S3 h3pc ⟨q3pc, q3sp, q3r, q3frame, q3val⟩
  have sp3 : S3.sp = s.sp - 368 := by rw [q3sp, sp2]
  have sp3n : S3.sp.toNat = s.sp.toNat - 368 := by rw [sp3]; simp [BitVec.toNat_sub]; omega
  have u0 : S3.regs 0 = s.regs 0 := by rw [q3r 0 (by decide) (by decide), t0]
  have u8 : (S3.regs 8).toNat = (S2.regs 8).toNat := by rw [q3r 8 (by decide) (by decide)]
  have u18 : S3.regs 18 = s.regs 18 := by rw [q3r 18 (by decide) (by decide), t18]
  have u28 : S3.regs 28 = s.regs 28 := by rw [q3r 28 (by decide) (by decide), t28]
  have hmem3 : ∀ a n, ((a + n ≤ (s.regs 0).toNat ∨ (s.regs 0).toNat + 32 ≤ a)) → S3.mem.readLE a n = S2.mem.readLE a n := by
    intro a n h
    apply q3frame.readLE
    simp only [Outside, and_true]; rw [t0]; exact h
  have hacc3 : ∀ a n w, S3.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [q3frame.accessible, hacc2]
  have hx29_3 : S3.mem.readLE (S3.sp.toNat - 8) 8 = (s.regs 29).toNat := by
    rw [sp3n, hmem3 _ _ (by omega)]
    have e : s.sp.toNat - 368 - 8 = s.sp.toNat - 376 := by omega
    rw [e]; exact hx29_2
  have hret_3 : S3.mem.readLE S3.sp.toNat 8 = (s.regs 30).toNat := by
    rw [sp3n, hmem3 _ _ (by omega)]; exact hret_2
  have mptr : (S3.regs 8).toNat = s.sp.toNat - 40 := by rw [u8, t8n]
  have mval : S3.mem.readLE (S3.regs 8).toNat 32 = s.mem.readLE (s.regs 3).toNat 32 := by
    rw [mptr, hmem3 _ _ (by omega)]; exact hclone
  have vz : S3.mem.readLE (s.regs 0).toNat 32 + 2 ^ 256 = s.mem.readLE (s.regs 1).toNat 32 + s.mem.readLE (s.regs 2).toNat 32 := by
    have := q3val
    rw [t0, t1, t2] at this
    rw [this, hmem2 _ _ (by omega) (by omega), hmem2 _ _ (by omega) (by omega)]
  have f3 : MemFrame s.mem S3.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 856, s.sp.toNat + 16)] := by
    rw [t0] at q3frame
    exact f2.trans q3frame (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)
  refine seg_mono (segEF S3 (s.regs 30) (s.regs 29) h3pc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · omega
  · rw [hacc3]; exact s.mem.accessible_mono hsw (by omega) (by omega)
  · rw [hacc3]; exact hrod
  · rw [u28]; exact hg1
  · rw [u28, hacc3]; exact hg2
  · rw [u28, hmem3 ((s.regs 28).toNat + 16) 8 (by omega), hmem2 ((s.regs 28).toNat + 16) 8 (by omega) (by omega)]; omega
  · rw [u28, sp3n]; omega
  · rw [u0]; exact hzb
  · rw [u0, hacc3]; exact hza
  · rw [mptr]; omega
  · rw [hacc3, mptr]; exact s.mem.accessible_sub hsw (Or.inl rfl) (by omega) (by omega)
  · rw [u0, sp3n]; omega
  · rw [mptr, sp3n]; omega
  · rw [mptr, u0]; omega
  · rw [mval]; exact hm32
  · exact hret_3
  · exact h30a
  · exact h30b
  · exact hx29_3
  intro S4 ⟨q4pc, q4sp, q40, q428, q429, q418, q430, q4val, q4frame⟩
  refine ⟨q4pc, ?_, ?_, ?_, ?_, q429, q430, ?_, ?_⟩
  · rw [q4sp, sp3]; exact BitVec.sub_add_cancel _ _
  · rw [q40, u0]
  · rw [q418, u18]
  · rw [q428, u28]
  · rw [u0, mval, vz] at q4val
    rw [q4val]
    simp [Fv256.F.addmodSpec, hm32]
  · rw [u0, sp3n] at q4frame
    exact f3.trans q4frame (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)


set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem gz (s : State) (hpc : s.pc = BitVec.ofNat 64 Extracted.entry)
    (hpre : Fv256.Arm64.AddModSeg.PreS s) (hnc : ¬ (s.mem.readLE ((s.regs 3).toNat + 24) 8 ≠ 0 ∧ s.mem.readLE ((s.regs 1).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8 ∧ s.mem.readLE ((s.regs 2).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8))
    (hm : s.mem.readLE (s.regs 3).toNat 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 8) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 16) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0) :
    ReachesRet Extracted.program (s.regs 30) s (Post s) := by
  obtain ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hdata, hgw, hzb, hza, hxb, hxa, hyb, hya, hmb, hma, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩ := hpre
  refine seg_trans (segA s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hdata, hgw, hzb, hza, hxb, hxa, hyb, hya, hmb, hma, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩ hnc) ?_
  intro S1 h1pc q1
  obtain ⟨r0, r1, r2, r3, r18, r28, r30, r8, sp1, hmem1, hacc1, hx29, hretS, hfr1⟩ := AF_of s S1 hsb hsc q1
  have sp1n : S1.sp.toNat = s.sp.toNat - 368 := by rw [sp1]; simp [BitVec.toNat_sub]; omega
  refine seg_mono (segZero S1 (s.regs 30) (s.regs 29) h1pc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · omega
  · omega
  · rw [r0]; exact hzb
  · rw [r0, hacc1]; exact hza
  · rw [r3]; exact hmb
  · rw [r3, hacc1]; exact hma
  · rw [r3, hmem1 _ _ (by omega), hmem1 (_ + 8) _ (by omega), hmem1 (_ + 16) _ (by omega), hmem1 (_ + 24) _ (by omega)]; exact hm
  · rw [r8, r3, hmem1 _ _ (by omega)]
  · rw [sp1n]; exact hretS
  · exact h30a
  · exact h30b
  · rw [r0, sp1n]; omega
  · rw [hacc1, sp1n]; exact s.mem.accessible_sub hsw (Or.inl rfl) (by omega) (by omega)
  · have e : s.sp.toNat - 368 - 8 = s.sp.toNat - 376 := by omega
    rw [sp1n, e]; exact hx29
  intro S2 ⟨q2pc, q2sp, q20, q228, q229, q218, q230, q2val, q2frame⟩
  have sp2 : S2.sp = s.sp := by rw [q2sp, sp1]; exact BitVec.sub_add_cancel _ _
  refine ⟨q2pc, sp2, ?_, ?_, ?_, q229, q230, ?_, ?_⟩
  · rw [q20, r0]
  · rw [q218, r18]
  · rw [q228, r28]
  · rw [r0] at q2val
    have hM : s.mem.readLE (s.regs 3).toNat 32 = 0 := by
      rw [Util.readLE_32, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2]
    simp [Fv256.F.addmodSpec, hM, q2val]
  · rw [r0] at q2frame
    exact hfr1.trans q2frame (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem gen_all (s : State) (hpc : s.pc = BitVec.ofNat 64 Extracted.entry)
    (hpre : Fv256.Arm64.AddModSeg.PreS s) (hnc : ¬ (s.mem.readLE ((s.regs 3).toNat + 24) 8 ≠ 0 ∧ s.mem.readLE ((s.regs 1).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8 ∧ s.mem.readLE ((s.regs 2).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8)) :
    ReachesRet Extracted.program (s.regs 30) s (Post s) := by
  by_cases hm0 : (s.mem.readLE (s.regs 3).toNat 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 8) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 16) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0)
  · exact gz s hpc hpre hnc hm0
  · by_cases hz : s.regs 3 = s.regs 0
    · by_cases hov : 2 ^ 256 ≤ s.mem.readLE (s.regs 1).toNat 32 + s.mem.readLE (s.regs 2).toNat 32
      · exact ga_ov s hpc hpre hnc hz hm0 hov
      · exact ga_nov s hpc hpre hnc hz hm0 (Nat.lt_of_not_le hov)
    · by_cases hov : 2 ^ 256 ≤ s.mem.readLE (s.regs 1).toNat 32 + s.mem.readLE (s.regs 2).toNat 32
      · exact gb_ov s hpc hpre hnc hz hm0 hov
      · exact gb_nov s hpc hpre hnc hz hm0 (Nat.lt_of_not_le hov)

end Fv256.Arm64.AddModComp2
