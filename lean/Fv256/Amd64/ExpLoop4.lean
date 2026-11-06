import Fv256.ExpProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecF
import Fv256.ExpMath
import Fv256.UtilF
import Fv256.Amd64.ExpSum

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.ExpLoop4

abbrev head4 : Nat := Fv256.Amd64.ExpSum.expEntry + 0x2cc

theorem head4_lt : head4 + 0x100 < 2 ^ 47 := by decide

/-- The state at the head of loop 1 of `Exp`: `k` bits processed, accumulator `r`, squared base `b`, remaining exponent word `w`;
the loop is entered with `sp0` the stack pointer at function entry; `z`, `ep` the receiver and exponent pointers, `ev` the low word of the base. -/
def Inv4 (s0 : State) (n z ep ev k r b w : Nat) (S : State) : Prop :=
  S.rip = BitVec.ofNat 64 head4 ∧
  k ≤ 256 ∧ r < 2 ^ 256 ∧ b < 2 ^ 256 ∧ w < 2 ^ 64 ∧ ev < 2 ^ 64 ∧
  S.regs 3 = BitVec.ofNat 64 k ∧ S.regs 7 = BitVec.ofNat 64 n ∧ S.regs 8 = BitVec.ofNat 64 w ∧
  S.regs 0 = BitVec.ofNat 64 z ∧
  S.regs 2 = s0.regs 4 - 104#64 ∧ S.regs 6 = s0.regs 4 - 72#64 ∧ S.regs 4 = s0.regs 4 - 144#64 ∧ S.regs 5 = s0.regs 4 - 8#64 ∧
  S.regs 14 = s0.regs 14 ∧ S.xmm 15 = 0 ∧
  S.mem.readLE ((s0.regs 4).toNat - 104) 32 = r ∧ S.mem.readLE ((s0.regs 4).toNat - 72) 32 = b ∧
  S.mem.readLE ((s0.regs 4).toNat + 8) 8 = z ∧ S.mem.readLE ((s0.regs 4).toNat + 24) 8 = ep ∧
  S.mem.readLE ((s0.regs 4).toNat - 120) 8 = n ∧ S.mem.readLE ((s0.regs 4).toNat - 16) 8 = ev ∧
  S.df = s0.df ∧ S.mxcsr = s0.mxcsr ∧ S.mem.readLE ((s0.regs 4).toNat - 8) 8 = (s0.regs 5).toNat ∧
  MemFrame s0.mem S.mem [((s0.regs 4).toNat - 0xa8, (s0.regs 4).toNat), ((s0.regs 4).toNat + 8, (s0.regs 4).toNat + 0x20)]

theorem slt_small (k n : Nat) (hk : k < n) (hn : n < 2 ^ 20) : ¬ (BitVec.ofNat 64 k).slt (BitVec.ofNat 64 n) = false := by
  simp only [BitVec.slt, decide_eq_false_iff_not, Decidable.not_not]
  have e : ∀ m : Nat, m < 2 ^ 20 → (BitVec.ofNat 64 m).toInt = m := by
    intro m hm
    rw [BitVec.toInt_eq_toNat_of_lt (by simp [BitVec.toNat_ofNat]; omega)]
    simp [BitVec.toNat_ofNat]; omega
  rw [e k (by omega), e n hn]; omega

theorem sub152_add8 (a : BitVec 64) : a - 152#64 + 8#64 = a - 144#64 := by bv_omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- Loop 1 of `Exp`: `t` iterations remain (`k + t = min n 256`). -/
theorem loop4 (s0 : State) (Q : State → Prop) (n z ep ev : Nat) (hn : n < 2 ^ 20)
    (hsp : 0x100 ≤ (s0.regs 4).toNat) (hspb : (s0.regs 4).toNat + 0x20 ≤ 2 ^ 48)
    (hwin : s0.mem.accessible ((s0.regs 4).toNat - 0xa8) (0xa8 + 0x20) true = true) :
    ∀ t k r b w (S : State), k + t = min n 256 → Inv4 s0 n z ep ev k r b w S →
      (∀ S', Inv4 s0 n z ep ev (min n 256) (Fv256.F.expIter t (r, b, w)).1 (Fv256.F.expIter t (r, b, w)).2.1
        (Fv256.F.expIter t (r, b, w)).2.2 S' → ReachesRet Fv256.ExpProg.program (retAddrOf s0) S' Q) →
      ReachesRet Fv256.ExpProg.program (retAddrOf s0) S Q := by
  intro t
  induction t with
  | zero =>
    intro k r b w S hkt hI hex
    exact hex S (by simpa [Fv256.F.expIter, ← hkt] using hI)
  | succ t ih =>
    intro k r b w S hkt hI hex
    obtain ⟨hpc, hk64, hr, hb, hw, hev, r3, r7, r8, r0, r2, r6, r4, r5, r14, x15, mr, mb, mz, mep, mn, mev, hdfS, hmxS, mbp, hfr⟩ := hI
    have hcode := head4_lt
    have hMa : S.mem.accessible ((s0.regs 4).toNat - 0xa8) (0xa8 + 0x20) true = true := by rw [hfr.accessible]; exact hwin
    have hk : k < min n 256 := by omega
    have hk1 : k < n := by omega
    have hk2 : k < 256 := by omega
    have hkt3 : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat]; omega
    have hnt : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
    have hcmp : ¬ (BitVec.ofNat 64 k).slt (BitVec.ofNat 64 n) = false := slt_small k n hk1 hn
    janus64_run [r3, r7, r8, r0, r2, r6, r4, r5, r14, mr, mb, mz, mep, mn, mev, mbp, hkt3, hnt] until [head4] calls [Fv256.Amd64.ExpSum.mul_summary, Fv256.Amd64.ExpSum.sq_summary]
    · rename_i ha h4 h5 h14 hx15 hdf hmx hm hf
      have hodd : ¬ (w % 2 = 1) := by
        have := hbr
        rw [Fv256.F.lsb_w32] at this
        simpa using this
      have e1 : (Fv256.F.expStep (r, b, w)).1 = r := by simp [Fv256.F.expStep, hodd]
      have e2 : (Fv256.F.expStep (r, b, w)).2.1 = b * b % 2 ^ 256 := rfl
      have e3 : (Fv256.F.expStep (r, b, w)).2.2 = w / 2 := rfl
      refine ih (k + 1) (Fv256.F.expStep (r, b, w)).1 (Fv256.F.expStep (r, b, w)).2.1 (Fv256.F.expStep (r, b, w)).2.2 _
        (by omega) ?inv (fun S' h => hex S' h)
      unfold Inv4
      rw [e1, e2, e3]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [setRegF, head4, Fv256.Amd64.ExpSum.expEntry]
      · omega
      · exact hr
      · exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · omega
      · exact hev
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]; exact Fv256.F.shr1_w64 w hw
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF, h4]; exact sub152_add8 _
      · simp [setRegF, h5, r5]
      · simp [setRegF, h14, r14]
      · simp [setRegF, hx15, x15]
      · rw [hf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mr
      · exact hm
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
        exact mev
      · first | exact hdfS | (simp [hdf, hdfS]; done)
      · first | exact hmxS | (simp [hmx, hmxS]; done)
      · rw [hf.readLE _ _ (by simp [Outside] <;> omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mbp
      · janus_frame
    · rename_i ha1 g0 g4 g5 g14 gx gdf gmx hmv hmf ha h4 h5 h14 hx15 hdf hmx hm hf
      have hodd : w % 2 = 1 := by
        have := hbr
        rw [Fv256.F.lsb_w32] at this
        simpa using this
      have e1 : (Fv256.F.expStep (r, b, w)).1 = r * b % 2 ^ 256 := by simp [Fv256.F.expStep, hodd]
      have e2 : (Fv256.F.expStep (r, b, w)).2.1 = b * b % 2 ^ 256 := rfl
      have e3 : (Fv256.F.expStep (r, b, w)).2.2 = w / 2 := rfl
      refine ih (k + 1) (Fv256.F.expStep (r, b, w)).1 (Fv256.F.expStep (r, b, w)).2.1 (Fv256.F.expStep (r, b, w)).2.2 _
        (by omega) ?inv2 (fun S' h => hex S' h)
      unfold Inv4
      rw [e1, e2, e3]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [setRegF, head4, Fv256.Amd64.ExpSum.expEntry]
      · omega
      · exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · omega
      · exact hev
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]; exact Fv256.F.shr1_w64 w hw
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF, h4]; exact sub152_add8 _
      · simp [setRegF, h5, g5, r5]
      · simp [setRegF, h14, g14, r14]
      · simp [setRegF, hx15, gx, x15]
      · rw [hf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact hmv
      · exact hm
      · rw [hf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        rw [hmf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mz
      · rw [hf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        rw [hmf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mep
      · rw [hf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        rw [hmf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mn
      · rw [hf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        rw [hmf.readLE _ _ (by simp [Outside]; omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mev
      · first | exact hdfS | (simp [hdf, gdf, hdfS]; done)
      · first | exact hmxS | (simp [hmx, gmx, hmxS]; done)
      · rw [hf.readLE _ _ (by simp [Outside] <;> omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        rw [hmf.readLE _ _ (by simp [Outside] <;> omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact mbp
      · janus_frame
