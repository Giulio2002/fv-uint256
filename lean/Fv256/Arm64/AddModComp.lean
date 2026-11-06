import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecF
import Fv256.Arm64.SegCompose
import Fv256.Arm64.AddModSeg
import Fv256.Arm64.AddModSegB

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.AddModSeg Fv256.Arm64.AddModSegB
open Fv256.Arm64.SegCompose (seg_trans seg_mono)

namespace Fv256.Arm64.AddModComp

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem gb_nov (s : State) (hpc : s.pc = BitVec.ofNat 64 Extracted.entry)
    (hpre : Fv256.Arm64.AddModSeg.PreS s)
    (hnc : ¬ (s.mem.readLE ((s.regs 3).toNat + 24) 8 ≠ 0 ∧ s.mem.readLE ((s.regs 1).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8 ∧ s.mem.readLE ((s.regs 2).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8))
    (hne : s.regs 3 ≠ s.regs 0)
    (hm : ¬ (s.mem.readLE (s.regs 3).toNat 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 8) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 16) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0))
    (hnov : s.mem.readLE (s.regs 1).toNat 32 + s.mem.readLE (s.regs 2).toNat 32 < 2 ^ 256) :
    ReachesRet Extracted.program (s.regs 30) s
      (fun s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 28 = s.regs 28 ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.addmodSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32)
          (s.mem.readLE (s.regs 3).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 856, s.sp.toNat + 16)]) := by
  obtain ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hdata, hgw, hzb, hza, hxb, hxa, hyb, hya, hmb, hma, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩ := hpre
  have hzm' := (hzm.resolve_left (fun h => hne h.symm))
  refine seg_trans (segA s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hdata, hgw, hzb, hza, hxb, hxa, hyb, hya, hmb, hma, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩ hnc) ?_
  intro S1 h1pc ⟨q1pc, q1sp, q1r, q18, q129, q1mem⟩
  have r0 : S1.regs 0 = s.regs 0 := q1r 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have r1 : S1.regs 1 = s.regs 1 := q1r 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have r2 : S1.regs 2 = s.regs 2 := q1r 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have r3 : S1.regs 3 = s.regs 3 := q1r 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have r28 : S1.regs 28 = s.regs 28 := q1r 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have r30 : S1.regs 30 = s.regs 30 := q1r 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hmem1 : ∀ a n, (a + n ≤ s.sp.toNat - 376 ∨ s.sp.toNat - 360 ≤ a) → S1.mem.readLE a n = s.mem.readLE a n := by
    intro a n h
    rw [q1mem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hacc1 : ∀ a n w, S1.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [q1mem]; simp
  have sp1 : S1.sp = s.sp - 368 := q1sp
  have sp1n : S1.sp.toNat = s.sp.toNat - 368 := by rw [sp1]; simp [BitVec.toNat_sub]; omega
  -- segment B: zero test, z != m
  refine seg_trans (segB S1 h1pc ?_ ?_ ?_ ?_ ?_) ?_
  · rw [r3, hmem1 _ _ (by omega), hmem1 (_ + 8) _ (by omega), hmem1 (_ + 16) _ (by omega), hmem1 (_ + 24) _ (by omega)]
    exact hm
  · rw [r3, r0]; exact hne
  · rw [r3]; exact hmb
  · rw [r3, hacc1]; exact hma
  · rw [q18, r3, hmem1 _ _ (by omega)]
  intro S2 h2pc ⟨q2pc, q2mem, q2sp, q28, q2r⟩
  have t0 : S2.regs 0 = s.regs 0 := by rw [q2r 0 (by decide) (by decide) (by decide), r0]
  have t1 : S2.regs 1 = s.regs 1 := by rw [q2r 1 (by decide) (by decide) (by decide), r1]
  have t2 : S2.regs 2 = s.regs 2 := by rw [q2r 2 (by decide) (by decide) (by decide), r2]
  have t3 : S2.regs 3 = s.regs 3 := by rw [q2r 3 (by decide) (by decide) (by decide), r3]
  have t28 : S2.regs 28 = s.regs 28 := by rw [q2r 28 (by decide) (by decide) (by decide), r28]
  have t30 : S2.regs 30 = s.regs 30 := by rw [q2r 30 (by decide) (by decide) (by decide), r30]
  have t8 : S2.regs 8 = s.regs 3 := by rw [q28, r3]
  have hmem2 : ∀ a n, (a + n ≤ s.sp.toNat - 376 ∨ s.sp.toNat - 360 ≤ a) → S2.mem.readLE a n = s.mem.readLE a n := by
    intro a n h; rw [q2mem]; exact hmem1 a n h
  have hacc2 : ∀ a n w, S2.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [q2mem]; exact hacc1 a n w
  have sp2n : S2.sp.toNat = s.sp.toNat - 368 := by rw [q2sp]; exact sp1n
  -- segment C: AddOverflow, no overflow
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
  have sp3 : S3.sp = s.sp - 368 := by rw [q3sp, q2sp, sp1]
  have sp3n : S3.sp.toNat = s.sp.toNat - 368 := by rw [sp3]; simp [BitVec.toNat_sub]; omega
  have u0 : S3.regs 0 = s.regs 0 := by rw [q3r 0 (by decide) (by decide), t0]
  have u8 : S3.regs 8 = s.regs 3 := by rw [q3r 8 (by decide) (by decide), t8]
  have u28 : S3.regs 28 = s.regs 28 := by rw [q3r 28 (by decide) (by decide), t28]
  have hmem3 : ∀ a n, ((a + n ≤ (s.regs 0).toNat ∨ (s.regs 0).toNat + 32 ≤ a)) → S3.mem.readLE a n = S2.mem.readLE a n := by
    intro a n h
    apply q3frame.readLE
    simp only [Outside, and_true]; rw [t0]; exact h
  have hacc3 : ∀ a n w, S3.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [q3frame.accessible, hacc2]
  refine seg_mono (segD S3 (s.regs 30) h3pc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
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
  · rw [u8]; exact hmb
  · rw [u8, hacc3]; exact hma
  · rw [u0]; omega
  · rw [u8]; omega
  · rw [hmem3 S3.sp.toNat 8 (by omega), q2mem, q1mem, sp3n]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    exact Nat.mod_eq_of_lt (by have := (s.regs 30).isLt; simpa using this)
  · exact h30a
  · exact h30b
  intro S4 ⟨q4pc, q4sp, q40, q428, q4val, q4frame⟩
  refine ⟨q4pc, ?_, ?_, ?_, ?_, ?_⟩
  · rw [q4sp, sp3]; exact BitVec.sub_add_cancel _ _
  · rw [q40, u0]
  · rw [q428, u28]
  · have vz : S3.mem.readLE (s.regs 0).toNat 32 = s.mem.readLE (s.regs 1).toNat 32 + s.mem.readLE (s.regs 2).toNat 32 := by
      have := q3val
      rw [t0, t1, t2] at this
      rw [this, hmem2 (s.regs 1).toNat 32 (by omega), hmem2 (s.regs 2).toNat 32 (by omega)]
    have vm : S3.mem.readLE (s.regs 3).toNat 32 = s.mem.readLE (s.regs 3).toNat 32 := by
      rw [hmem3 (s.regs 3).toNat 32 (by omega), hmem2 (s.regs 3).toNat 32 (by omega)]
    rw [u0, u8] at q4val
    rw [q4val, vz, vm]
    simp [Fv256.F.addmodSpec, Fv256.B.modSpec]
  · have f1 : MemFrame s.mem S2.mem [(s.sp.toNat - 376, s.sp.toNat - 360)] := by
      rw [q2mem, q1mem]
      exact ((MemFrame.refl s.mem _).writeLE _ (r := (s.sp.toNat - 376, s.sp.toNat - 360)) (by simp) (by dsimp only; omega)
        (by dsimp only; omega)).writeLE _ (r := (s.sp.toNat - 376, s.sp.toNat - 360)) (by simp) (by dsimp only; omega)
        (by dsimp only; omega)
    rw [t0] at q3frame
    have f12 : MemFrame s.mem S3.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 856, s.sp.toNat + 16)] :=
      f1.trans q3frame (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)
    rw [u0, sp3n] at q4frame
    exact f12.trans q4frame (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)

end Fv256.Arm64.AddModComp
