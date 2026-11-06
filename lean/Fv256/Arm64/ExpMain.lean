import Fv256.Arm64.ExpSum
import Fv256.Arm64.ExpLoop1
import Fv256.Arm64.ExpLoop2
import Fv256.Arm64.ExpLoop3
import Fv256.Arm64.ExpLoop4
import Fv256.Arm64.ExpLoopLem
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecF
import Fv256.ExpMath
import Fv256.ExpFinal
import Fv256.ExpPro
import Fv256.UtilF
import Fv256.Arm64.ExpEntry

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.ExpMain

/-- The postcondition of `exp_summary`. -/
def PostE (s s' : State) : Prop :=
  s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
    s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
    s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.expSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32) ∧
    MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 168, s.sp.toNat),
      (s.sp.toNat + 8, s.sp.toNat + 32)]

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- From the head of loop 4 with all `n` bits processed: copy the accumulator to `z` and return. -/
theorem after4 (s : State) (n z ep base0 r b w : Nat) (S : State)
    (hz : z = (s.regs 0).toNat) (hep : ep = (s.regs 2).toNat) (hn : n ≤ 256)
    (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 56)
    (hal : s.sp.toNat % 16 = 0) (hsp : 336 ≤ s.sp.toNat) (hspb : s.sp.toNat + 40 ≤ 2 ^ 48)
    (hwin : s.mem.accessible (s.sp.toNat - 168) (168 + 40) true = true)
    (hzb : (s.regs 0).toNat + 32 ≤ 2 ^ 48) (hza : s.mem.accessible (s.regs 0).toNat 32 true = true)
    (hdz : Apart (s.regs 0).toNat 32 (s.sp.toNat - 168) 208)
    (hI : Fv256.Arm64.ExpLoop4.Inv4 s n z ep base0 (min n 256) r b w S)
    (hr : r = Fv256.F.expSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32)) :
    ReachesRet Fv256.Arm64.ExpProg.program (s.regs 30) S (PostE s) := by
  obtain ⟨hpc, hk64, hr', hb, hw, hb0, hsp', r0, r1, r3, r4, r18, r28, r29, mr, mb, mz, mep, mn, mb0, mret, mfp, hfr⟩ := hI
  have hMa : S.mem.accessible (s.sp.toNat - 168) (168 + 40) true = true := by rw [hfr.accessible]; exact hwin
  simp only [Fv256.Arm64.ExpLoop4.head4, reduceSegAddr, Nat.reduceAdd] at hpc
  have hMa' : S.mem.accessible (S.sp.toNat - 8) 208 true = true := by
    rw [hsp', show s.sp.toNat - 160 - 8 = s.sp.toNat - 168 by omega]; exact hMa
  have hspb' : S.sp.toNat + 200 ≤ 2 ^ 48 := by omega
  have hspl' : 168 ≤ S.sp.toNat := by omega
  have hspal' : S.sp.toNat % 16 = 0 := by omega
  have hmin : min n 256 = n := by omega
  simp only [hmin] at r1 r3
  have hnt : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  subst hz
  have mret' : S.mem.readLE S.sp.toNat 8 = (s.regs 30).toNat := by rw [hsp']; exact mret
  have mfp' : S.mem.readLE (S.sp.toNat - 8) 8 = (s.regs 29).toNat := by
    rw [hsp', show s.sp.toNat - 160 - 8 = s.sp.toNat - 168 by omega]; exact mfp
  have hdzu : (s.regs 0).toNat + 32 ≤ S.sp.toNat - 8 ∨ S.sp.toNat + 200 ≤ (s.regs 0).toNat := by
    unfold Apart at hdz; omega
  janus_run [r0, r1, r3, r4, r18, r28, r29, mr, mb, mz, mep, mn, mb0, hnt, mret', mfp']
  unfold PostE
  simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
  refine ⟨trivial, ?_, ?_, ?_, ?_, trivial, trivial, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := s.sp.isLt
    omega
  · rw [r0]; simp
  · exact r18
  · exact r28
  · rw [Fv256.F.copy32 S.mem _ _ _ _ _ rfl rfl rfl, show BitVec.toNat S.sp + 56 = s.sp.toNat - 104 by omega, mr]
    exact hr
  · janus_frame


/-- one stage of the square-and-multiply: bits `lo .. hi` of an exponent of bit length `n`, with exponent word `e` -/
def st (n lo hi r b e : Nat) : Nat × Nat × Nat := Fv256.F.expIter (min n hi - min n lo) (r, b, e)

def chain3 (n r b e3 : Nat) : Nat := (st n 192 256 r b e3).1
def chain2 (n r b e2 e3 : Nat) : Nat := chain3 n (st n 128 192 r b e2).1 (st n 128 192 r b e2).2.1 e3
def chain1 (n r b e1 e2 e3 : Nat) : Nat := chain2 n (st n 64 128 r b e1).1 (st n 64 128 r b e1).2.1 e2 e3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- From the head of loop 3 with all of its bits processed: load the last exponent word and run loop 4. -/
theorem after3 (s : State) (n z ep base0 r b w e3 : Nat) (S : State)
    (hz : z = (s.regs 0).toNat) (hep : ep = (s.regs 2).toNat) (hn : n ≤ 256)
    (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 56)
    (hal : s.sp.toNat % 16 = 0) (hsp : 336 ≤ s.sp.toNat) (hspb : s.sp.toNat + 40 ≤ 2 ^ 48)
    (hwin : s.mem.accessible (s.sp.toNat - 168) (168 + 40) true = true)
    (hzb : (s.regs 0).toNat + 32 ≤ 2 ^ 48) (hza : s.mem.accessible (s.regs 0).toNat 32 true = true)
    (hdz : Apart (s.regs 0).toNat 32 (s.sp.toNat - 168) 208)
    (hyb : (s.regs 2).toNat + 32 ≤ 2 ^ 48) (hya : s.mem.accessible (s.regs 2).toNat 32 false = true)
    (hdy : Apart (s.regs 2).toNat 32 (s.sp.toNat - 168) 208)
    (hI : Fv256.Arm64.ExpLoop3.Inv3 s n z ep base0 (min n 192) r b w S)
    (he3 : s.mem.readLE (ep + 24) 8 = e3) (he3b : e3 < 2 ^ 64)
    (hr : chain3 n r b e3 = Fv256.F.expSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32)) :
    ReachesRet Fv256.Arm64.ExpProg.program (s.regs 30) S (PostE s) := by
  have hk43 : min n 192 + (min n 256 - min n 192) = min n 256 := by omega
  have hI' := hI
  obtain ⟨hpc, hk64, hr', hb, hw, hb0, hsp', r0, r1, r2, r3, r4, r18, r28, r29, mr, mb, mz, mep, mn, mb0, mret, mfp, hfr⟩ := hI
  have hMa : S.mem.accessible (s.sp.toNat - 168) (168 + 40) true = true := by rw [hfr.accessible]; exact hwin
  simp only [Fv256.Arm64.ExpLoop3.head3, reduceSegAddr, Nat.reduceAdd] at hpc
  have hMa' : S.mem.accessible (S.sp.toNat - 8) 208 true = true := by
    rw [hsp', show s.sp.toNat - 160 - 8 = s.sp.toNat - 168 by omega]; exact hMa
  have hspb' : S.sp.toNat + 200 ≤ 2 ^ 48 := by omega
  have hspl' : 168 ≤ S.sp.toNat := by omega
  have hspal' : S.sp.toNat % 16 = 0 := by omega
  have hmin : min n 192 = min n 192 := rfl
  have hnt : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  have hkt : (BitVec.ofNat 64 (min n 192)).toNat = min n 192 := by rw [BitVec.toNat_ofNat]; omega
  subst hep
  have he3S : S.mem.readLE ((s.regs 2).toNat + 24) 8 = e3 := by
    rw [hfr.readLE _ _ (by simp only [Outside, and_true]; unfold Apart at hdy; omega)]; exact he3
  janus_run [r0, r1, r2, r3, r4, r18, r28, r29, mr, mb, mz, mep, mn, mb0, hnt, hkt, he3S] until [Fv256.Arm64.ExpLoop4.head4]
  all_goals (
    have key := Fv256.Arm64.ExpLoop4.loop4 s (PostE s) n z (s.regs 2).toNat base0 (by omega) hal hsp hspb hwin
      (min n 256 - min n 192) (min n 192) r b e3
    apply key
    · exact hk43
    · unfold Fv256.Arm64.ExpLoop4.Inv4
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · omega
      · exact hr'
      · exact hb
      · exact he3b
      · exact hb0
      · exact hsp'
      all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
      · exact r0
      · exact r1
      · exact r3
      · exact r18
      · exact r28
      · exact r29
      · exact mr
      · exact mb
      · exact mz
      · exact mep
      · exact mn
      · exact mb0
      · exact mret
      · exact mfp
      · exact hfr
    · intro S' hI4
      exact after4 s n z (s.regs 2).toNat base0 _ _ _ S' hz rfl hn h30a h30b hal hsp hspb hwin hzb hza hdz hI4 hr)



set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- From the head of loop 2 with all of its bits processed: load the third exponent word and run loop 3. -/
theorem after2 (s : State) (n z ep base0 r b w e2 e3 : Nat) (S : State)
    (hz : z = (s.regs 0).toNat) (hep : ep = (s.regs 2).toNat) (hn : n ≤ 256)
    (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 56)
    (hal : s.sp.toNat % 16 = 0) (hsp : 336 ≤ s.sp.toNat) (hspb : s.sp.toNat + 40 ≤ 2 ^ 48)
    (hwin : s.mem.accessible (s.sp.toNat - 168) (168 + 40) true = true)
    (hzb : (s.regs 0).toNat + 32 ≤ 2 ^ 48) (hza : s.mem.accessible (s.regs 0).toNat 32 true = true)
    (hdz : Apart (s.regs 0).toNat 32 (s.sp.toNat - 168) 208)
    (hyb : (s.regs 2).toNat + 32 ≤ 2 ^ 48) (hya : s.mem.accessible (s.regs 2).toNat 32 false = true)
    (hdy : Apart (s.regs 2).toNat 32 (s.sp.toNat - 168) 208)
    (hI : Fv256.Arm64.ExpLoop2.Inv2 s n z ep base0 (min n 128) r b w S)
    (he2 : s.mem.readLE (ep + 16) 8 = e2) (he2b : e2 < 2 ^ 64)
    (he3 : s.mem.readLE (ep + 24) 8 = e3) (he3b : e3 < 2 ^ 64)
    (hr : chain2 n r b e2 e3 = Fv256.F.expSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32)) :
    ReachesRet Fv256.Arm64.ExpProg.program (s.regs 30) S (PostE s) := by
  have hk43 : min n 128 + (min n 192 - min n 128) = min n 192 := by omega
  have hI' := hI
  obtain ⟨hpc, hk64, hr', hb, hw, hb0, hsp', r0, r1, r2, r3, r4, r18, r28, r29, mr, mb, mz, mep, mn, mb0, mret, mfp, hfr⟩ := hI
  have hMa : S.mem.accessible (s.sp.toNat - 168) (168 + 40) true = true := by rw [hfr.accessible]; exact hwin
  simp only [Fv256.Arm64.ExpLoop2.head2, reduceSegAddr, Nat.reduceAdd] at hpc
  have hMa' : S.mem.accessible (S.sp.toNat - 8) 208 true = true := by
    rw [hsp', show s.sp.toNat - 160 - 8 = s.sp.toNat - 168 by omega]; exact hMa
  have hspb' : S.sp.toNat + 200 ≤ 2 ^ 48 := by omega
  have hspl' : 168 ≤ S.sp.toNat := by omega
  have hspal' : S.sp.toNat % 16 = 0 := by omega
  have hmin : min n 128 = min n 128 := rfl
  have hnt : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  have hkt : (BitVec.ofNat 64 (min n 128)).toNat = min n 128 := by rw [BitVec.toNat_ofNat]; omega
  subst hep
  have he2S : S.mem.readLE ((s.regs 2).toNat + 16) 8 = e2 := by
    rw [hfr.readLE _ _ (by simp only [Outside, and_true]; unfold Apart at hdy; omega)]; exact he2
  janus_run [r0, r1, r2, r3, r4, r18, r28, r29, mr, mb, mz, mep, mn, mb0, hnt, hkt, he2S] until [Fv256.Arm64.ExpLoop3.head3]
  all_goals (
    have key := Fv256.Arm64.ExpLoop3.loop3 s (PostE s) n z (s.regs 2).toNat base0 (by omega) hal hsp hspb hwin
      (min n 192 - min n 128) (min n 128) r b e2
    apply key
    · exact hk43
    · unfold Fv256.Arm64.ExpLoop3.Inv3
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · omega
      · exact hr'
      · exact hb
      · exact he2b
      · exact hb0
      · exact hsp'
      all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
      · exact r0
      · exact r1
      · exact r2
      · exact r3
      · exact r18
      · exact r28
      · exact r29
      · exact mr
      · exact mb
      · exact mz
      · exact mep
      · exact mn
      · exact mb0
      · exact mret
      · exact mfp
      · exact hfr
    · intro S' hI4
      exact after3 s n z (s.regs 2).toNat base0 _ _ _ e3 S' hz rfl hn h30a h30b hal hsp hspb hwin hzb hza hdz hyb hya hdy hI4 he3 he3b hr)



set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- From the head of loop 1 with all of its bits processed: either return (even base), or load the second exponent word and run loop 2. -/
theorem after1 (s : State) (n z ep base0 r b w e1 e2 e3 : Nat) (S : State)
    (hz : z = (s.regs 0).toNat) (hep : ep = (s.regs 2).toNat) (hn : n ≤ 256)
    (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 56)
    (hal : s.sp.toNat % 16 = 0) (hsp : 336 ≤ s.sp.toNat) (hspb : s.sp.toNat + 40 ≤ 2 ^ 48)
    (hwin : s.mem.accessible (s.sp.toNat - 168) (168 + 40) true = true)
    (hzb : (s.regs 0).toNat + 32 ≤ 2 ^ 48) (hza : s.mem.accessible (s.regs 0).toNat 32 true = true)
    (hdz : Apart (s.regs 0).toNat 32 (s.sp.toNat - 168) 208)
    (hyb : (s.regs 2).toNat + 32 ≤ 2 ^ 48) (hya : s.mem.accessible (s.regs 2).toNat 32 false = true)
    (hdy : Apart (s.regs 2).toNat 32 (s.sp.toNat - 168) 208)
    (hI : Fv256.Arm64.ExpLoop1.Inv1 s n z ep base0 (min n 64) r b w S)
    (he1 : s.mem.readLE (ep + 8) 8 = e1) (he1b : e1 < 2 ^ 64)
    (he2 : s.mem.readLE (ep + 16) 8 = e2) (he2b : e2 < 2 ^ 64)
    (he3 : s.mem.readLE (ep + 24) 8 = e3) (he3b : e3 < 2 ^ 64)
    (hev : base0 % 2 = 0 → n ≤ 8)
    (hr : chain1 n r b e1 e2 e3 = Fv256.F.expSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32)) :
    ReachesRet Fv256.Arm64.ExpProg.program (s.regs 30) S (PostE s) := by
  have hk43 : min n 64 + (min n 128 - min n 64) = min n 128 := by omega
  subst hz
  have hI' := hI
  obtain ⟨hpc, hk64, hr', hb, hw, hb0, hsp', r0, r1, r2, r3, r4, r5, r18, r28, r29, mr, mb, mz, mep, mn, mb0, mret, mfp, hfr⟩ := hI
  have hMa : S.mem.accessible (s.sp.toNat - 168) (168 + 40) true = true := by rw [hfr.accessible]; exact hwin
  simp only [Fv256.Arm64.ExpLoop1.head1, reduceSegAddr, Nat.reduceAdd] at hpc
  have hMa' : S.mem.accessible (S.sp.toNat - 8) 208 true = true := by
    rw [hsp', show s.sp.toNat - 160 - 8 = s.sp.toNat - 168 by omega]; exact hMa
  have hspb' : S.sp.toNat + 200 ≤ 2 ^ 48 := by omega
  have hspl' : 168 ≤ S.sp.toNat := by omega
  have hspal' : S.sp.toNat % 16 = 0 := by omega
  have hmin : min n 64 = min n 64 := rfl
  have hnt : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  have hkt : (BitVec.ofNat 64 (min n 64)).toNat = min n 64 := by rw [BitVec.toNat_ofNat]; omega
  subst hep
  have he1S : S.mem.readLE ((s.regs 2).toNat + 8) 8 = e1 := by
    rw [hfr.readLE _ _ (by simp only [Outside, and_true]; unfold Apart at hdy; omega)]; exact he1
  have mret' : S.mem.readLE S.sp.toNat 8 = (s.regs 30).toNat := by rw [hsp']; exact mret
  have mfp' : S.mem.readLE (S.sp.toNat - 8) 8 = (s.regs 29).toNat := by
    rw [hsp', show s.sp.toNat - 160 - 8 = s.sp.toNat - 168 by omega]; exact mfp
  have hdzu : (s.regs 0).toNat + 32 ≤ S.sp.toNat - 8 ∨ S.sp.toNat + 200 ≤ (s.regs 0).toNat := by
    unfold Apart at hdz; omega
  janus_run [mret', mfp', r0, r1, r2, r3, r4, r5, r18, r28, r29, mr, mb, mz, mep, mn, mb0, hnt, hkt, he1S] until [Fv256.Arm64.ExpLoop2.head2]
  · -- even base, first exit
    rename_i c1 hl c3
    have hb0e : base0 % 2 = 0 := by
      have := hl
      rw [Fv256.F.lsb_w64] at this
      simpa using this
    have hn8 := hev hb0e
    have hch : chain1 n r b e1 e2 e3 = r := by
      have z1 : min n 128 - min n 64 = 0 := by omega
      have z2 : min n 192 - min n 128 = 0 := by omega
      have z3 : min n 256 - min n 192 = 0 := by omega
      simp only [chain1, chain2, chain3, st, z1, z2, z3, Fv256.F.stage_zero]
    have hr' : r = Fv256.F.expSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32) := by rw [← hr, hch]
    unfold PostE
    simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
    refine ⟨trivial, ?_, ?_, ?_, ?_, trivial, trivial, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := s.sp.isLt
      omega
    · rw [r0]; simp
    · exact r18
    · exact r28
    · rw [Fv256.F.copy32 S.mem _ _ _ _ _ rfl rfl rfl, show BitVec.toNat S.sp + 56 = s.sp.toNat - 104 by omega, mr]
      exact hr'
    · janus_frame
  · -- odd base, first exit
    have key := Fv256.Arm64.ExpLoop2.loop2 s (PostE s) n (s.regs 0).toNat (s.regs 2).toNat base0 (by omega) hal hsp hspb hwin
      (min n 128 - min n 64) (min n 64) r b e1
    apply key
    · exact hk43
    · unfold Fv256.Arm64.ExpLoop2.Inv2
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · omega
      · exact hr'
      · exact hb
      · exact he1b
      · exact hb0
      · exact hsp'
      all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
      · exact r0
      · exact r1
      · exact r2
      · exact r3
      · exact r18
      · exact r28
      · exact r29
      · exact mr
      · exact mb
      · exact mz
      · exact mep
      · exact mn
      · exact mb0
      · exact mret
      · exact mfp
      · exact hfr
    · intro S' hI4
      exact after2 s n (s.regs 0).toNat (s.regs 2).toNat base0 _ _ _ e2 e3 S' rfl rfl hn h30a h30b hal hsp hspb hwin hzb hza hdz hyb hya hdy hI4 he2 he2b he3 he3b hr
  · -- even base, second exit
    rename_i c1 c2 hl c4
    have hb0e : base0 % 2 = 0 := by
      have := hl
      rw [Fv256.F.lsb_w64] at this
      simpa using this
    have hn8 := hev hb0e
    have hch : chain1 n r b e1 e2 e3 = r := by
      have z1 : min n 128 - min n 64 = 0 := by omega
      have z2 : min n 192 - min n 128 = 0 := by omega
      have z3 : min n 256 - min n 192 = 0 := by omega
      simp only [chain1, chain2, chain3, st, z1, z2, z3, Fv256.F.stage_zero]
    have hr' : r = Fv256.F.expSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32) := by rw [← hr, hch]
    unfold PostE
    simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
    refine ⟨trivial, ?_, ?_, ?_, ?_, trivial, trivial, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := s.sp.isLt
      omega
    · rw [r0]; simp
    · exact r18
    · exact r28
    · rw [Fv256.F.copy32 S.mem _ _ _ _ _ rfl rfl rfl, show BitVec.toNat S.sp + 56 = s.sp.toNat - 104 by omega, mr]
      exact hr'
    · janus_frame
  · -- odd base, second exit
    have key := Fv256.Arm64.ExpLoop2.loop2 s (PostE s) n (s.regs 0).toNat (s.regs 2).toNat base0 (by omega) hal hsp hspb hwin
      (min n 128 - min n 64) (min n 64) r b e1
    apply key
    · exact hk43
    · unfold Fv256.Arm64.ExpLoop2.Inv2
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · omega
      · exact hr'
      · exact hb
      · exact he1b
      · exact hb0
      · exact hsp'
      all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
      · exact r0
      · exact r1
      · exact r2
      · exact r3
      · exact r18
      · exact r28
      · exact r29
      · exact mr
      · exact mb
      · exact mz
      · exact mep
      · exact mn
      · exact mb0
      · exact mret
      · exact mfp
      · exact hfr
    · intro S' hI4
      exact after2 s n (s.regs 0).toNat (s.regs 2).toNat base0 _ _ _ e2 e3 S' rfl rfl hn h30a h30b hal hsp hspb hwin hzb hza hdz hyb hya hdy hI4 he2 he2b he3 he3b hr


/-- the state at the head of loop 1, as produced by the prologue (`nreg`/`nmem` are the computed bit length, in a register and in its stack slot) -/
def S0 (s : State) (nreg : BitVec 64) (nmem : Nat) (fl : Flags) : State :=
  { regs :=
      setReg (setReg (setReg (setReg (setReg (setReg (setReg (setReg (setReg s.regs 1 0#64) 3 nreg) 4
        (BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 1)) 8))) 5
        (BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 2)) 8))) 6
        (BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 1) + 24) 8))) 16
        (BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 28) + 16) 8))) 17 (s.sp - 32#64)) 27 1009776#64) 29 (s.sp - 168#64),
    sp := s.sp - 160#64, pc := 775096#64,
    flags := fl,
    mem :=
      (((((((((((((s.mem.writeLE (BitVec.toNat s.sp - 160) 8 (BitVec.toNat (s.regs 30))).writeLE (BitVec.toNat s.sp - 168) 8
        (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp - 104) 8 1).writeLE (BitVec.toNat s.sp - 96) 8 0).writeLE
        (BitVec.toNat s.sp - 88) 8 0).writeLE (BitVec.toNat s.sp - 80) 8 0).writeLE (BitVec.toNat s.sp - 72) 8
        (s.mem.readLE (BitVec.toNat (s.regs 1)) 8)).writeLE (BitVec.toNat s.sp - 64) 8
        (s.mem.readLE (BitVec.toNat (s.regs 1) + 8) 8)).writeLE (BitVec.toNat s.sp - 56) 8
        (s.mem.readLE (BitVec.toNat (s.regs 1) + 16) 8)).writeLE (BitVec.toNat s.sp - 48) 8
        (s.mem.readLE (BitVec.toNat (s.regs 1) + 24) 8)).writeLE (BitVec.toNat s.sp + 8) 8 (BitVec.toNat (s.regs 0))).writeLE
        (BitVec.toNat s.sp + 24) 8 (BitVec.toNat (s.regs 2))).writeLE (BitVec.toNat s.sp - 120) 8 nmem).writeLE
        (BitVec.toNat s.sp - 16) 8 (s.mem.readLE (BitVec.toNat (s.regs 1)) 8),
    dczid := s.dczid, vregs := s.vregs, tpidr := s.tpidr, fpcr := s.fpcr, fpsr := s.fpsr, excl := s.excl,
    exclPass := s.exclPass }

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem inv_start (s : State) (n : Nat) (nreg : BitVec 64) (nmem : Nat) (fl : Flags)
    (hnreg : nreg = BitVec.ofNat 64 n) (hnmem : nmem % 18446744073709551616 = n) (hn : n < 2 ^ 20)
    (hal : s.sp.toNat % 16 = 0) (hsp : 336 ≤ s.sp.toNat) (hspb : s.sp.toNat + 40 ≤ 2 ^ 48)
    (hxb : (s.regs 1).toNat + 32 ≤ 2 ^ 48) (hdx : Apart (s.regs 1).toNat 32 (s.sp.toNat - 168) 208)
    (hdz : Apart (s.regs 0).toNat 32 (s.sp.toNat - 168) 208)
    (hyb : (s.regs 2).toNat + 32 ≤ 2 ^ 48) (hdy : Apart (s.regs 2).toNat 32 (s.sp.toNat - 168) 208) :
    Fv256.Arm64.ExpLoop1.Inv1 s n (s.regs 0).toNat (s.regs 2).toNat (s.mem.readLE (s.regs 1).toNat 8) 0 1
      (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 8) (S0 s nreg nmem fl) := by
  unfold Fv256.Arm64.ExpLoop1.Inv1 S0
  have hx0 := Util.readLE8_lt s.mem (s.regs 1).toNat
  have hxd0 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 8)
  have hxd1 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 16)
  have hxd2 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 24)
  have hy0 := Util.readLE8_lt s.mem (s.regs 2).toNat
  unfold Apart at hdx hdz hdy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · rfl
  · omega
  · decide
  · have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 1)) 32; simpa using this
  · exact hy0
  · exact hx0
  · simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := s.sp.isLt; omega
  · simp
  · simp
  · exact hnreg
  · -- res
    rw [Util.readLE_32]
    have a1 : BitVec.toNat s.sp - 104 + 8 = BitVec.toNat s.sp - 96 := by omega
    have a2 : BitVec.toNat s.sp - 104 + 16 = BitVec.toNat s.sp - 88 := by omega
    have a3 : BitVec.toNat s.sp - 104 + 24 = BitVec.toNat s.sp - 80 := by omega
    rw [a1, a2, a3]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  · rw [Util.readLE_32]
    have a1 : BitVec.toNat s.sp - 72 + 8 = BitVec.toNat s.sp - 64 := by omega
    have a2 : BitVec.toNat s.sp - 72 + 16 = BitVec.toNat s.sp - 56 := by omega
    have a3 : BitVec.toNat s.sp - 72 + 24 = BitVec.toNat s.sp - 48 := by omega
    rw [a1, a2, a3]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [Util.readLE_32]
    have e1 : (s.mem.readLE (BitVec.toNat (s.regs 1)) 8) % 256 ^ 8 = s.mem.readLE (BitVec.toNat (s.regs 1)) 8 := Nat.mod_eq_of_lt (by simpa using hx0)
    have e2 : (s.mem.readLE (BitVec.toNat (s.regs 1) + 8) 8) % 256 ^ 8 = s.mem.readLE (BitVec.toNat (s.regs 1) + 8) 8 := Nat.mod_eq_of_lt (by simpa using hxd0)
    have e3 : (s.mem.readLE (BitVec.toNat (s.regs 1) + 16) 8) % 256 ^ 8 = s.mem.readLE (BitVec.toNat (s.regs 1) + 16) 8 := Nat.mod_eq_of_lt (by simpa using hxd1)
    have e4 : (s.mem.readLE (BitVec.toNat (s.regs 1) + 24) 8) % 256 ^ 8 = s.mem.readLE (BitVec.toNat (s.regs 1) + 24) 8 := Nat.mod_eq_of_lt (by simpa using hxd2)
    rw [e1, e2, e3, e4]
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (s.regs 0).isLt; simpa using this)
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (s.regs 2).isLt; simpa using this)
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact hnmem
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt hx0
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (s.regs 30).isLt; simpa using this)
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (s.regs 29).isLt; simpa using this)
  · janus_frame


set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- Everything after the prologue: from the head of loop 1 with `n` the bit length of the exponent. -/
theorem run_from_S0 (s : State) (n : Nat) (nreg : BitVec 64) (nmem : Nat) (fl : Flags)
    (hnreg : nreg = BitVec.ofNat 64 n) (hnmem : nmem % 18446744073709551616 = n)
    (hbl : Fv256.Spec.bitLen (s.mem.readLE (s.regs 2).toNat 32) = n)
    (hev : s.mem.readLE (s.regs 1).toNat 8 % 2 = 0 → n ≤ 8)
    (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 56)
    (hal : s.sp.toNat % 16 = 0) (hsp : 336 ≤ s.sp.toNat) (hspb : s.sp.toNat + 40 ≤ 2 ^ 48)
    (hwin : s.mem.accessible (s.sp.toNat - 168) (168 + 40) true = true)
    (hzb : (s.regs 0).toNat + 32 ≤ 2 ^ 48) (hza : s.mem.accessible (s.regs 0).toNat 32 true = true)
    (hdz : Apart (s.regs 0).toNat 32 (s.sp.toNat - 168) 208)
    (hxb : (s.regs 1).toNat + 32 ≤ 2 ^ 48) (hdx : Apart (s.regs 1).toNat 32 (s.sp.toNat - 168) 208)
    (hyb : (s.regs 2).toNat + 32 ≤ 2 ^ 48) (hya : s.mem.accessible (s.regs 2).toNat 32 false = true)
    (hdy : Apart (s.regs 2).toNat 32 (s.sp.toNat - 168) 208) :
    ReachesRet Fv256.Arm64.ExpProg.program (s.regs 30) (S0 s nreg nmem fl) (PostE s) := by
  have he0 := Util.readLE8_lt s.mem (s.regs 2).toNat
  have he1 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 8)
  have he2 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 16)
  have he3 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 24)
  have hE : s.mem.readLE (s.regs 2).toNat 32 = s.mem.readLE (s.regs 2).toNat 8 + 2 ^ 64 * s.mem.readLE ((s.regs 2).toNat + 8) 8
      + 2 ^ 128 * s.mem.readLE ((s.regs 2).toNat + 16) 8 + 2 ^ 192 * s.mem.readLE ((s.regs 2).toNat + 24) 8 := by
    rw [Util.readLE_32]
  have hB := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 1).toNat 32
  simp only [Nat.reducePow] at hB
  have hEl := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 2).toNat 32
  simp only [Nat.reducePow] at hEl
  have hn256 : n ≤ 256 := by rw [← hbl]; exact Fv256.F.bitLen_le _ 256 (by simpa using hEl)
  have hnlt : n < 2 ^ 20 := by omega
  have hEn : s.mem.readLE (s.regs 2).toNat 8 + 2 ^ 64 * s.mem.readLE ((s.regs 2).toNat + 8) 8
      + 2 ^ 128 * s.mem.readLE ((s.regs 2).toNat + 16) 8 + 2 ^ 192 * s.mem.readLE ((s.regs 2).toNat + 24) 8 < 2 ^ n := by
    rw [← hE, ← hbl]; exact Fv256.F.bitLen_lt _
  have htot := Fv256.F.exp_total (s.mem.readLE (s.regs 1).toNat 32) _ _ _ _ n hB he0 he1 he2 he3 hn256 hEn
  have hr : chain1 n (Fv256.F.expIter (min n 64) (1, s.mem.readLE (s.regs 1).toNat 32, s.mem.readLE (s.regs 2).toNat 8)).1
      (Fv256.F.expIter (min n 64) (1, s.mem.readLE (s.regs 1).toNat 32, s.mem.readLE (s.regs 2).toNat 8)).2.1
      (s.mem.readLE ((s.regs 2).toNat + 8) 8) (s.mem.readLE ((s.regs 2).toNat + 16) 8) (s.mem.readLE ((s.regs 2).toNat + 24) 8)
      = Fv256.F.expSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32) := by
    have hs1 := Fv256.Arm64.ExpEntry.expIter_lt (min n 64) 1 _ (s.mem.readLE (s.regs 2).toNat 8) (by decide) hB
    have hs2 := Fv256.Arm64.ExpEntry.expIter_lt (min n 128 - min n 64) _ _ (s.mem.readLE ((s.regs 2).toNat + 8) 8) hs1.1 hs1.2
    have hs3 := Fv256.Arm64.ExpEntry.expIter_lt (min n 192 - min n 128) _ _ (s.mem.readLE ((s.regs 2).toNat + 16) 8) hs2.1 hs2.2
    have hs4 := Fv256.Arm64.ExpEntry.expIter_lt (min n 256 - min n 192) _ _ (s.mem.readLE ((s.regs 2).toNat + 24) 8) hs3.1 hs3.2
    have hfin : (chain1 n (Fv256.F.expIter (min n 64) (1, s.mem.readLE (s.regs 1).toNat 32, s.mem.readLE (s.regs 2).toNat 8)).1
      (Fv256.F.expIter (min n 64) (1, s.mem.readLE (s.regs 1).toNat 32, s.mem.readLE (s.regs 2).toNat 8)).2.1
      (s.mem.readLE ((s.regs 2).toNat + 8) 8) (s.mem.readLE ((s.regs 2).toNat + 16) 8) (s.mem.readLE ((s.regs 2).toNat + 24) 8)) % 2 ^ 256
        = (s.mem.readLE (s.regs 1).toNat 32 ^ (s.mem.readLE (s.regs 2).toNat 8 + 2 ^ 64 * s.mem.readLE ((s.regs 2).toNat + 8) 8
      + 2 ^ 128 * s.mem.readLE ((s.regs 2).toNat + 16) 8 + 2 ^ 192 * s.mem.readLE ((s.regs 2).toNat + 24) 8)) % 2 ^ 256 := htot
    unfold Fv256.F.expSpec
    rw [hE, ← hfin]
    exact (Nat.mod_eq_of_lt hs4.1).symm
  have hk0 : 0 + min n 64 = min n 64 := Nat.zero_add _
  have key := Fv256.Arm64.ExpLoop1.loop1 s (PostE s) n (s.regs 0).toNat (s.regs 2).toNat (s.mem.readLE (s.regs 1).toNat 8)
    hnlt hal hsp hspb hwin (min n 64) 0 1 (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 8)
  apply key (S0 s nreg nmem fl) hk0
  · exact inv_start s n nreg nmem fl hnreg hnmem hnlt hal hsp hspb hxb hdx hdz hyb hdy
  · intro S' hI
    exact after1 s n (s.regs 0).toNat (s.regs 2).toNat (s.mem.readLE (s.regs 1).toNat 8) _ _ _
      (s.mem.readLE ((s.regs 2).toNat + 8) 8) (s.mem.readLE ((s.regs 2).toNat + 16) 8) (s.mem.readLE ((s.regs 2).toNat + 24) 8)
      S' rfl rfl hn256 h30a h30b hal hsp hspb hwin hzb hza hdz hyb hya hdy hI rfl he1 rfl he2 rfl he3 hev hr


set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem exp_summary :
    Summary Fv256.Arm64.ExpProg.program Fv256.Arm64.ExpSum.expEntry
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 32 ∧ StackOK s 168 40 ∧ 336 ≤ s.sp.toNat ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 168) 208 ∧
        (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
        (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
        (s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧
        Apart (s.regs 0).toNat 32 (s.sp.toNat - 168) 208 ∧ Apart (s.regs 1).toNat 32 (s.sp.toNat - 168) 208 ∧
        Apart (s.regs 2).toNat 32 (s.sp.toNat - 168) 208 ∧
        Fv256.Arm64.ExpProg.program.DataLoaded s.mem)
      PostE := by
  intro s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, ⟨hsal, hsb, hsc, hsw⟩, hsp, hdg, hzb, hza, hxb, hxa, hyb, hya, hdz, hdx, hdy, hdl⟩
  have hal := hsal
  have hspb := hsc
  have hwin := hsw
  have hx0 := Util.readLE8_lt s.mem (s.regs 1).toNat
  have hx1 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 8)
  have hx2 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 16)
  have hx3 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 24)
  have he0 := Util.readLE8_lt s.mem (s.regs 2).toNat
  have he1 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 8)
  have he2 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 16)
  have he3 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 24)
  have hE : s.mem.readLE (s.regs 2).toNat 32 = s.mem.readLE (s.regs 2).toNat 8 + 2 ^ 64 * s.mem.readLE ((s.regs 2).toNat + 8) 8
      + 2 ^ 128 * s.mem.readLE ((s.regs 2).toNat + 16) 8 + 2 ^ 192 * s.mem.readLE ((s.regs 2).toNat + 24) 8 := by
    rw [Util.readLE_32]
  have hBs : s.mem.readLE (s.regs 1).toNat 32 = s.mem.readLE (s.regs 1).toNat 8 + 2 ^ 64 * s.mem.readLE ((s.regs 1).toNat + 8) 8
      + 2 ^ 128 * s.mem.readLE ((s.regs 1).toNat + 16) 8 + 2 ^ 192 * s.mem.readLE ((s.regs 1).toNat + 24) 8 := by
    rw [Util.readLE_32]
  have cl0 := Fv256.Arm64.ExpEntry.clz_le _ he0
  have cl1 := Fv256.Arm64.ExpEntry.clz_le _ he1
  have cl2 := Fv256.Arm64.ExpEntry.clz_le _ he2
  have cl3 := Fv256.Arm64.ExpEntry.clz_le _ he3
  janus_data hdl [hsw]
  janus_run [Util.readLE_32] until [Fv256.Arm64.ExpSum.expEntry + 0x118]
  · -- limb 0, odd base
    refine run_from_S0 s (64 - Janus.Arm64.clzNat 64 (s.mem.readLE (s.regs 2).toNat 8)) _ _ _ (Fv256.Arm64.ExpEntry.nreg0 _ cl0) ?nm ?bl (Fv256.Arm64.ExpEntry.hev_odd _ _ hbr) h30a h30b hal hsp hspb hwin hzb hza hdz hxb hdx hyb hya hdy
    case nm => exact Fv256.Arm64.ExpEntry.nm0a _ cl0
    case bl => rw [hE]; exact Fv256.Arm64.ExpEntry.bl0 _ _ _ _ he0 (by janus_assumption) (by janus_assumption) (by janus_assumption)
  · -- limb 0, even base, n ≤ 8
    refine run_from_S0 s (64 - Janus.Arm64.clzNat 64 (s.mem.readLE (s.regs 2).toNat 8)) _ _ _ (Fv256.Arm64.ExpEntry.nreg0 _ cl0) ?nm ?bl ?hv h30a h30b hal hsp hspb hwin hzb hza hdz hxb hdx hyb hya hdy
    case nm => exact Fv256.Arm64.ExpEntry.nm0c _ cl0
    case bl => rw [hE]; exact Fv256.Arm64.ExpEntry.bl0 _ _ _ _ he0 (by janus_assumption) (by janus_assumption) (by janus_assumption)
    case hv => intro _; omega
  · -- limb 0, even base, large exponent
    unfold PostE
    simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
    have hB0 : s.mem.readLE (s.regs 1).toNat 32 % 2 = 0 := by
      have := Fv256.Arm64.ExpEntry.even_lsb _ (by janus_assumption)
      rw [hBs]; omega
    have h0 : 0 = Fv256.F.expSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32) := by
      apply Fv256.Arm64.ExpEntry.early _ _ hB0
      rw [hE, Fv256.Arm64.ExpEntry.bl0 _ _ _ _ he0 (by janus_assumption) (by janus_assumption) (by janus_assumption)]; omega
    refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, ?_, ?_⟩
    · rw [Util.readLE_32]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      simp only [Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
      exact h0
    · janus_frame
  · -- limb 1, odd base
    refine run_from_S0 s (64 - Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 2).toNat + 8) 8) + 64) _ _ _ (Fv256.Arm64.ExpEntry.nreg _ 64 cl1 (by omega)) ?nm ?bl (Fv256.Arm64.ExpEntry.hev_odd _ _ hbr) h30a h30b hal hsp hspb hwin hzb hza hdz hxb hdx hyb hya hdy
    case nm => exact Fv256.Arm64.ExpEntry.nmK _ 64 cl1 (by omega)
    case bl => rw [hE]; exact Fv256.Arm64.ExpEntry.bl1 _ _ _ _ he0 he1 (by janus_assumption) (by janus_assumption) (by janus_assumption)
  · -- limb 1, even base, large exponent
    unfold PostE
    simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
    have hB0 : s.mem.readLE (s.regs 1).toNat 32 % 2 = 0 := by
      have := Fv256.Arm64.ExpEntry.even_lsb _ (by janus_assumption)
      rw [hBs]; omega
    have h0 : 0 = Fv256.F.expSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32) := by
      apply Fv256.Arm64.ExpEntry.early _ _ hB0
      rw [hE, Fv256.Arm64.ExpEntry.bl1 _ _ _ _ he0 he1 (by janus_assumption) (by janus_assumption) (by janus_assumption)]; omega
    refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, ?_, ?_⟩
    · rw [Util.readLE_32]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      simp only [Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
      exact h0
    · janus_frame
  · -- limb 2, odd base
    refine run_from_S0 s (64 - Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 2).toNat + 16) 8) + 128) _ _ _ (Fv256.Arm64.ExpEntry.nreg _ 128 cl2 (by omega)) ?nm ?bl (Fv256.Arm64.ExpEntry.hev_odd _ _ hbr) h30a h30b hal hsp hspb hwin hzb hza hdz hxb hdx hyb hya hdy
    case nm => exact Fv256.Arm64.ExpEntry.nmK _ 128 cl2 (by omega)
    case bl => rw [hE]; exact Fv256.Arm64.ExpEntry.bl2 _ _ _ _ he0 he1 he2 (by janus_assumption) (by janus_assumption)
  · -- limb 2, even base, large exponent
    unfold PostE
    simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
    have hB0 : s.mem.readLE (s.regs 1).toNat 32 % 2 = 0 := by
      have := Fv256.Arm64.ExpEntry.even_lsb _ (by janus_assumption)
      rw [hBs]; omega
    have h0 : 0 = Fv256.F.expSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32) := by
      apply Fv256.Arm64.ExpEntry.early _ _ hB0
      rw [hE, Fv256.Arm64.ExpEntry.bl2 _ _ _ _ he0 he1 he2 (by janus_assumption) (by janus_assumption)]; omega
    refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, ?_, ?_⟩
    · rw [Util.readLE_32]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      simp only [Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
      exact h0
    · janus_frame
  · -- limb 3, odd base
    refine run_from_S0 s (64 - Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 2).toNat + 24) 8) + 192) _ _ _ (Fv256.Arm64.ExpEntry.nreg _ 192 cl3 (by omega)) ?nm ?bl (Fv256.Arm64.ExpEntry.hev_odd _ _ hbr) h30a h30b hal hsp hspb hwin hzb hza hdz hxb hdx hyb hya hdy
    case nm => exact Fv256.Arm64.ExpEntry.nmK _ 192 cl3 (by omega)
    case bl => rw [hE]; exact Fv256.Arm64.ExpEntry.bl3 _ _ _ _ he0 he1 he2 he3 (by janus_assumption)
  · -- limb 3, even base, large exponent
    unfold PostE
    simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
    have hB0 : s.mem.readLE (s.regs 1).toNat 32 % 2 = 0 := by
      have := Fv256.Arm64.ExpEntry.even_lsb _ (by janus_assumption)
      rw [hBs]; omega
    have h0 : 0 = Fv256.F.expSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32) := by
      apply Fv256.Arm64.ExpEntry.early _ _ hB0
      rw [hE, Fv256.Arm64.ExpEntry.bl3 _ _ _ _ he0 he1 he2 he3 (by janus_assumption)]; omega
    refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, ?_, ?_⟩
    · rw [Util.readLE_32]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      simp only [Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
      exact h0
    · janus_frame

end Fv256.Arm64.ExpMain
