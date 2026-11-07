import Fv256.Arm64.SfdTopSpec
import Fv256.Arm64.SfdFdF
import Fv256.Arm64.SfdDecode
import Fv256.SfdTopMath

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdTopSpec

namespace Fv256.Arm64.SfdTop

abbrev sfd : Nat := segAddr Fv256.Arm64.SfdProg.program "github.com/holiman/uint256.(*Int).SetFromDecimal"

/-- the addresses of the harness binary -/
def cfg : SfdCfg := SfdCfg.mk
  (0x1b5c10)
  (0x1b5b60)
  (0x1b6540)
  (0xdc840)
  (0xf6940)
  (0xf6920)
  (0xf5940)
  (0x1b5eb0)
  (0x1e34c0)
  (0xeb483)
  (0xf490b)
  (Fv256.Arm64.SfdProg.program.contractAddr "runtime.mallocgc")
  (Fv256.Arm64.SfdProg.program.contractAddr "runtime.memmove")
  (Fv256.Arm64.SfdProg.program.contractAddr "runtime.newobject")
  (Fv256.Arm64.SfdProg.program.contractAddr "runtime.gcWriteBarrier1")
  (Fv256.Arm64.SfdProg.program.contractAddr "runtime.gcWriteBarrier2")

/-- the state inside `SetFromDecimal`'s frame (80 bytes below the entry `SP`), before `fromDecimal` runs:
only the window `[lo, hi)` was written, the four spill words hold LR, FP, `z`, `pS`. -/
def TopSt (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS : BitVec 64)
    (s S : State) : Prop :=
  S.sp = s.sp - 80#64 ∧ S.regs 29 = s.sp - 88#64 ∧ S.regs 28 = s.regs 28 ∧ S.regs 18 = s.regs 18 ∧
  MemFrame s.mem S.mem [(lo, hi)] ∧
  S.mem.readLE (s.sp.toNat - 80) 8 = (s.regs 30).toNat ∧ S.mem.readLE (s.sp.toNat - 88) 8 = (s.regs 29).toNat ∧
  S.mem.readLE (s.sp.toNat + 8) 8 = z.toNat ∧ S.mem.readLE (s.sp.toNat + 16) 8 = pS.toNat ∧
  S.mem.readLE (s.sp.toNat - 8) 8 = s.mem.readLE (s.sp.toNat - 8) 8 ∧ S.mem.readLE s.sp.toNat 8 = s.mem.readLE s.sp.toNat 8 ∧
  Env cfg R R2 T b L lo hi S

theorem pe_zero (b : Nat → Nat) (n : Nat) (h : n = 0) : plusEnd b n = 0 := by
  unfold plusEnd; simp [h]

theorem pe_plus (b : Nat → Nat) (n : Nat) (h : 0 < n) (hb : b 0 = 43) : plusEnd b n = 1 := by
  unfold plusEnd; simp [h, hb]

theorem pe_not (b : Nat → Nat) (n : Nat) (hb : b 0 ≠ 43) : plusEnd b n = 0 := by
  unfold plusEnd; simp [hb]

/-- the memory after the prologue stores -/
def proMem (s : State) (z pS : BitVec 64) : Janus.Arm64.Memory :=
  (((s.mem.writeLE (s.sp.toNat - 80) 8 (s.regs 30).toNat).writeLE (s.sp.toNat - 88) 8 (s.regs 29).toNat).writeLE
    (s.sp.toNat + 16) 8 pS.toNat).writeLE (s.sp.toNat + 8) 8 z.toNat

theorem topSt_intro (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s S : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (hsp : S.sp = s.sp - 80#64) (h29 : S.regs 29 = s.sp - 88#64) (h28 : S.regs 28 = s.regs 28)
    (h18 : S.regs 18 = s.regs 18) (hmem : S.mem = proMem s z pS) : TopSt R R2 T b L lo hi z pS s S := by
  obtain ⟨hl1, hl2, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hsp80 : (s.sp - 80#64).toNat = s.sp.toNat - 80 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hmf : MemFrame s.mem S.mem [(lo, hi)] := by
    rw [hmem]; unfold proMem
    repeat' first
      | exact MemFrame.refl _ _
      | refine MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  refine ⟨hsp, h29, h28, h18, hmf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmem]; unfold proMem
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (BitVec.isLt _)
  · rw [hmem]; unfold proMem
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (BitVec.isLt _)
  · rw [hmem]; unfold proMem
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (BitVec.isLt _)
  · rw [hmem]; unfold proMem
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (BitVec.isLt _)
  · rw [hmem]; unfold proMem
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  · rw [hmem]; unfold proMem
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  · exact Fv256.Arm64.SfdEnv.Env.frame0 hMod.1 hEnv ⟨by rw [hsp, hsp80]; omega, by rw [hsp, hsp80]; omega, by rw [hsp, hsp80]; omega⟩
      (by rw [h28]) hmf (by omega)

theorem byte_eq (x : Nat) (hx : x < 256) : (BitVec.setWidth 32 (BitVec.ofNat 64 x)).toNat = 43 ↔ x = 43 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem sub1_lt (nS : BitVec 64) (h0 : nS.toNat ≠ 0) (h1 : nS.toNat ≤ 2 ^ 48) : (nS - 1#64).toNat = nS.toNat - 1 := by
  simp only [BitVec.toNat_sub]; simp only [Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod]; omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- entry, stack check, frame, spills and the `+` skip: to pc `0xb89f4` -/
theorem top_pro (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 0xb89b0)
    (hpre : TopPre cfg R R2 T b L lo hi z pS nS s) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (BitVec.ofNat 64 0xb89f4) s
      (fun S => TopSt R R2 T b L lo hi z pS s S ∧ S.regs 0 = z ∧
        S.regs 2 = nS - BitVec.ofNat 64 (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
        (∃ k, k ≤ plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
          (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < nS.toNat → k = plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
          S.regs 1 = pS + BitVec.ofNat 64 k)) := by
  have hpre' := hpre
  obtain ⟨hl1, hl2, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hacc : s.mem.accessible (s.sp.toNat - 88) 120 true = true :=
    Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  have hg : s.mem.readLE ((s.regs 28).toNat + 16) 8 < lo := e8
  have hmod16 := Nat.mod_eq_of_lt (show (s.regs 28).toNat + 16 < 2 ^ 64 by omega)
  have hb0 : Fv256.C.bytesAt s.mem pS.toNat 0 = s.mem.readLE pS.toNat 1 := rfl
  have hintro : ∀ S : State, S.sp = s.sp - 80#64 → S.regs 29 = s.sp - 88#64 → S.regs 28 = s.regs 28 →
      S.regs 18 = s.regs 18 → S.mem = proMem s z pS → TopSt R R2 T b L lo hi z pS s S :=
    fun S a1 a2 a3 a4 a5 => topSt_intro R R2 T b L lo hi z pS nS s S hpre' a1 a2 a3 a4 a5
  by_cases hn : nS = 0
  · subst hn
    have hpe : plusEnd (Fv256.C.bytesAt s.mem pS.toNat) (0#64).toNat = 0 := pe_zero _ _ rfl
    have hpe0 : plusEnd (Fv256.C.bytesAt s.mem pS.toNat) 0 = 0 := pe_zero _ _ rfl
    janus_run [hpc, h0, h1, h2, hacc, hg, e7, e4, hmod16, hpe] until [0xb89f4]
    all_goals (
      refine ⟨hintro _ rfl (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl, ?_⟩
      rw [hpe0]
      exact ⟨by simp, 0, Nat.le_refl _, fun h => absurd h (by omega), by simp⟩)
  · have hn' : nS.toNat ≠ 0 := fun h => hn (BitVec.eq_of_toNat_eq h)
    have hpA' : s.mem.accessible pS.toNat 1 false = true :=
      Arm64.Memory.accessible_mono _ (hpA.resolve_left hn') (by omega) (by omega)
    have hbl := Arm64.Memory.readLE_lt s.mem pS.toNat 1
    by_cases hb : (BitVec.setWidth 32 (BitVec.ofNat 64 (s.mem.readLE pS.toNat 1))).toNat = 43
    · have hb' : s.mem.readLE pS.toNat 1 = 43 := (byte_eq _ (by simpa using hbl)).1 hb
      have hpe : plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = 1 := pe_plus _ _ (by omega) (by rw [hb0]; exact hb')
      have hm : (nS - 1#64).toNat < 2 ^ 63 := by rw [sub1_lt nS hn' (by omega)]; omega
      have hne : 1 < nS.toNat → nS - 1#64 ≠ 0#64 := fun hlt h => by
        have h' := congrArg BitVec.toNat h
        rw [sub1_lt nS hn' (by omega)] at h'
        simp at h'
        omega
      janus_run [hpc, h0, h1, h2, hn, hacc, hg, e7, e4, hmod16, hpA', hb, hpe] until [0xb89f4]
      all_goals (
        refine ⟨hintro _ rfl (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl, ?_⟩
        by_cases hlt : 1 < nS.toNat
        · exact ⟨1, Nat.le_refl _, fun _ => rfl, by rw [Fv256.TopMath.asr_and1 _ hm, if_neg (hne hlt)]⟩
        · have h1 : nS = 1#64 := BitVec.eq_of_toNat_eq (by simp; omega)
          have h0 : nS - 1#64 = 0#64 := by rw [h1]; decide
          exact ⟨0, by omega, fun h => by omega, by rw [Fv256.TopMath.asr_and1 _ hm, if_pos h0]⟩)
    · have hpe : plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = 0 :=
        pe_not _ _ (by rw [hb0]; intro h; exact hb ((byte_eq _ (by simpa using hbl)).2 h))
      janus_run [hpc, h0, h1, h2, hn, hacc, hg, e7, e4, hmod16, hpA', hb, hpe] until [0xb89f4]
      all_goals (
        refine ⟨hintro _ rfl (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl, ?_⟩
        exact ⟨0, Nat.le_refl _, fun _ => rfl, by simp⟩)

end Fv256.Arm64.SfdTop
