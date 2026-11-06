import Fv256.Arm64.ExpSum
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecF
import Fv256.ExpMath
import Fv256.UtilF
import Fv256.Arm64.ExpLoopLem

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.ExpLoop3

abbrev head3 : Nat := Fv256.Arm64.ExpSum.expEntry + 0x1f0

/-- The state at the head of loop 1 of `Exp`: `k` bits processed, accumulator `r`, squared base `b`, remaining exponent word `w`;
`s0` is the state at function entry, `z`, `ep` the receiver and exponent pointers, `n` the bit length, `base0` the low word of the base. -/
def Inv3 (s0 : State) (n z ep base0 k r b w : Nat) (S : State) : Prop :=
  S.pc = BitVec.ofNat 64 head3 ∧
  k ≤ 192 ∧ r < 2 ^ 256 ∧ b < 2 ^ 256 ∧ w < 2 ^ 64 ∧ base0 < 2 ^ 64 ∧
  S.sp.toNat = s0.sp.toNat - 160 ∧
  S.regs 0 = BitVec.ofNat 64 z ∧ S.regs 1 = BitVec.ofNat 64 k ∧ S.regs 2 = BitVec.ofNat 64 ep ∧
  S.regs 3 = BitVec.ofNat 64 n ∧ S.regs 4 = BitVec.ofNat 64 w ∧
  S.regs 18 = s0.regs 18 ∧ S.regs 28 = s0.regs 28 ∧ S.regs 29 = s0.sp - 168#64 ∧
  S.mem.readLE (s0.sp.toNat - 104) 32 = r ∧ S.mem.readLE (s0.sp.toNat - 72) 32 = b ∧
  S.mem.readLE (s0.sp.toNat + 8) 8 = z ∧ S.mem.readLE (s0.sp.toNat + 24) 8 = ep ∧
  S.mem.readLE (s0.sp.toNat - 120) 8 = n ∧ S.mem.readLE (s0.sp.toNat - 16) 8 = base0 ∧
  S.mem.readLE (s0.sp.toNat - 160) 8 = (s0.regs 30).toNat ∧ S.mem.readLE (s0.sp.toNat - 168) 8 = (s0.regs 29).toNat ∧
  MemFrame s0.mem S.mem [(s0.sp.toNat - 168, s0.sp.toNat), (s0.sp.toNat + 8, s0.sp.toNat + 32)]

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- Loop 1 of `Exp`: `t` iterations remain (`k + t = min n 192`). -/
theorem loop3 (s0 : State) (Q : State → Prop) (n z ep base0 : Nat) (hn : n < 2 ^ 20)
    (hal : s0.sp.toNat % 16 = 0) (hsp : 336 ≤ s0.sp.toNat) (hspb : s0.sp.toNat + 40 ≤ 2 ^ 48)
    (hwin : s0.mem.accessible (s0.sp.toNat - 168) (168 + 32) true = true) :
    ∀ t k r b w (S : State), k + t = min n 192 → Inv3 s0 n z ep base0 k r b w S →
      (∀ S', Inv3 s0 n z ep base0 (min n 192) (Fv256.F.expIter t (r, b, w)).1 (Fv256.F.expIter t (r, b, w)).2.1
        (Fv256.F.expIter t (r, b, w)).2.2 S' → ReachesRet Fv256.Arm64.ExpProg.program (s0.regs 30) S' Q) →
      ReachesRet Fv256.Arm64.ExpProg.program (s0.regs 30) S Q := by
  intro t
  induction t with
  | zero =>
    intro k r b w S hkt hI hex
    exact hex S (by simpa [Fv256.F.expIter, ← hkt] using hI)
  | succ t ih =>
    intro k r b w S hkt hI hex
    obtain ⟨hpc, hk64, hr, hb, hw, hb0, hsp', r0, r1, r2, r3, r4, r18, r28, r29, mr, mb, mz, mep, mn, mb0, mret, mfp, hfr⟩ := hI
    have hk : k < min n 192 := by omega
    have hk1 : k < n := by omega
    have hk2 : k < 192 := by omega
    have hkt3 : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat]; omega
    have hnt : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
    have hMa : S.mem.accessible (s0.sp.toNat - 168) (168 + 32) true = true := by rw [hfr.accessible]; exact hwin
    simp only [head3, reduceSegAddr, Nat.reduceAdd] at hpc
    have hMa' : S.mem.accessible (S.sp.toNat - 8) 200 true = true := by
      rw [hsp', show s0.sp.toNat - 160 - 8 = s0.sp.toNat - 168 by omega]; exact hMa
    have hspb' : S.sp.toNat + 200 ≤ 2 ^ 48 := by omega
    have hspl' : 168 ≤ S.sp.toNat := by omega
    have hspal' : S.sp.toNat % 16 = 0 := by omega
    janus_run [r0, r1, r2, r3, r4, r18, r28, r29, mr, mb, mz, mep, mn, mb0, hkt3, hnt] until [head3] calls [Fv256.Arm64.ExpSum.mul_summary, Fv256.Arm64.ExpSum.sq_summary]
    · -- even bit: only the squaring
      rename_i c1 c2 ha lpc lsp l18 l28 l29 l30 hv hf
      have hodd : ¬ (w % 2 = 1) := by
        have := hbr
        rw [Fv256.F.lsb_w64] at this
        simpa using this
      have e1 : (Fv256.F.expStep (r, b, w)).1 = r := by simp [Fv256.F.expStep, hodd]
      have e2 : (Fv256.F.expStep (r, b, w)).2.1 = b * b % 2 ^ 256 := rfl
      have e3 : (Fv256.F.expStep (r, b, w)).2.2 = w / 2 := rfl
      have d168 : S.sp.toNat + 168 = s0.sp.toNat + 8 := by omega
      have d184 : S.sp.toNat + 184 = s0.sp.toNat + 24 := by omega
      have d40 : S.sp.toNat + 40 = s0.sp.toNat - 120 := by omega
      have d144 : S.sp.toNat + 144 = s0.sp.toNat - 16 := by omega
      refine ih (k + 1) (Fv256.F.expStep (r, b, w)).1 (Fv256.F.expStep (r, b, w)).2.1 (Fv256.F.expStep (r, b, w)).2.2 _
        (by omega) ?inv (fun S' h => hex S' h)
      unfold Inv3
      rw [e1, e2, e3]
      simp (config := { decide := true }) only [setReg_apply, ↓reduceIte] at lpc lsp l18 l28 l29 l30
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · omega
      · exact hr
      · exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · omega
      · exact hb0
      · exact hsp'
      all_goals (try simp (config := { decide := true }) only [setReg_apply, ↓reduceIte])
      · rw [d168, mz]
      · exact Fv256.Arm64.ExpLoopLem.inc1 k
      · rw [d184, mep]
      · rw [d40, mn]
      · exact Fv256.Arm64.ExpLoopLem.lsr1 w hw
      · rw [l18]; exact r18
      · rw [l28]; exact r28
      · rw [l29]; exact r29
      · rw [hf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mr
      · rw [show s0.sp.toNat - 72 = S.sp.toNat + 88 by omega, hv, show S.sp.toNat + 88 = s0.sp.toNat - 72 by omega, mb]
        simp [Spec.mul, Spec.W]
      · rw [hf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mz
      · rw [hf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mep
      · rw [hf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mn
      · rw [hf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mb0
      · rw [hf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mret
      · rw [hf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mfp
      · janus_frame
    · -- odd bit: multiply, then square
      rename_i c1 c2 ha1 m1 m2 m3 m4 m5 m6 mv mf ha2 lpc lsp l18 l28 l29 l30 hv hf
      simp (config := { decide := true }) only [setReg_apply, ↓reduceIte] at m3 m4 m5
      have hodd : w % 2 = 1 := by
        have := hbr
        rw [Fv256.F.lsb_w64] at this
        simpa using this
      have e1 : (Fv256.F.expStep (r, b, w)).1 = r * b % 2 ^ 256 := by simp [Fv256.F.expStep, hodd]
      have e2 : (Fv256.F.expStep (r, b, w)).2.1 = b * b % 2 ^ 256 := rfl
      have e3 : (Fv256.F.expStep (r, b, w)).2.2 = w / 2 := rfl
      have d168 : S.sp.toNat + 168 = s0.sp.toNat + 8 := by omega
      have d184 : S.sp.toNat + 184 = s0.sp.toNat + 24 := by omega
      have d40 : S.sp.toNat + 40 = s0.sp.toNat - 120 := by omega
      have d144 : S.sp.toNat + 144 = s0.sp.toNat - 16 := by omega
      refine ih (k + 1) (Fv256.F.expStep (r, b, w)).1 (Fv256.F.expStep (r, b, w)).2.1 (Fv256.F.expStep (r, b, w)).2.2 _
        (by omega) ?inv2 (fun S' h => hex S' h)
      unfold Inv3
      rw [e1, e2, e3]
      simp (config := { decide := true }) only [setReg_apply, ↓reduceIte] at lpc lsp l18 l28 l29 l30
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · omega
      · exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · omega
      · exact hb0
      · exact hsp'
      all_goals (try simp (config := { decide := true }) only [setReg_apply, ↓reduceIte])
      · rw [d168, mz]
      · exact Fv256.Arm64.ExpLoopLem.inc1 k
      · rw [d184, mep]
      · rw [d40, mn]
      · exact Fv256.Arm64.ExpLoopLem.lsr1 w hw
      · rw [l18, m3]; exact r18
      · rw [l28, m4]; exact r28
      · rw [l29, m5]; exact r29
      · rw [hf.readLE _ _ (by simp [Outside]; omega), show s0.sp.toNat - 104 = S.sp.toNat + 56 by omega, mv,
          show S.sp.toNat + 56 = s0.sp.toNat - 104 by omega, show S.sp.toNat + 88 = s0.sp.toNat - 72 by omega, mr, mb]
        simp [Spec.mul, Spec.W]
      · rw [show s0.sp.toNat - 72 = S.sp.toNat + 88 by omega, hv, show S.sp.toNat + 88 = s0.sp.toNat - 72 by omega, mb]
        simp [Spec.mul, Spec.W]
      · rw [hf.readLE _ _ (by simp [Outside]; omega), mf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mz
      · rw [hf.readLE _ _ (by simp [Outside]; omega), mf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mep
      · rw [hf.readLE _ _ (by simp [Outside]; omega), mf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mn
      · rw [hf.readLE _ _ (by simp [Outside]; omega), mf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mb0
      · rw [hf.readLE _ _ (by simp [Outside]; omega), mf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mret
      · rw [hf.readLE _ _ (by simp [Outside]; omega), mf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mfp
      · janus_frame

end Fv256.Arm64.ExpLoop3
