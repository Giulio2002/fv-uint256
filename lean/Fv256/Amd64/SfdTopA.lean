import Fv256.Amd64.SfdTopBr
import Fv256.Amd64.SfdDecode
import Fv256.SfdTopMath

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd
  Fv256.Amd64.SfdTopSpec Fv256.Amd64.SfdTopCfg Fv256.Amd64.SfdTopBr

namespace Fv256.Amd64.SfdTop

abbrev sfd : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).SetFromDecimal"

/-- the state inside `SetFromDecimal`'s frame (64 bytes below the return slot), before `fromDecimal` runs:
only the window `[lo, hi)` was written; the spill words hold BP, `z`, `pS`. -/
def TopSt (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS : BitVec 64)
    (s S : State) : Prop :=
  S.regs 4 = s.regs 4 - 64#64 ∧ S.regs 5 = s.regs 4 - 8#64 ∧ S.regs 14 = s.regs 14 ∧ S.xmm 15 = 0 ∧ S.df = false ∧
  S.fsBase = s.fsBase ∧ MemFrame s.mem S.mem [(lo, hi)] ∧
  S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧
  S.mem.readLE ((s.regs 4).toNat + 8) 8 = z.toNat ∧ S.mem.readLE ((s.regs 4).toNat + 16) 8 = pS.toNat ∧
  S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 ∧
  Fv256.Amd64.SfdEnv.Env R R2 T b L lo hi S

theorem pe_zero (b : Nat → Nat) (n : Nat) (h : n = 0) : plusEnd b n = 0 := by
  unfold plusEnd; simp [h]

theorem pe_plus (b : Nat → Nat) (n : Nat) (h : 0 < n) (hb : b 0 = 43) : plusEnd b n = 1 := by
  unfold plusEnd; simp [h, hb]

theorem pe_not (b : Nat → Nat) (n : Nat) (hb : b 0 ≠ 43) : plusEnd b n = 0 := by
  unfold plusEnd; simp [hb]

/-- the memory after the prologue stores -/
def proMem (s : State) (z pS : BitVec 64) : Janus.Arm64.Memory :=
  ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat + 16) 8 pS.toNat).writeLE
    ((s.regs 4).toNat + 8) 8 z.toNat

theorem topSt_intro (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s S : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (h4 : S.regs 4 = s.regs 4 - 64#64) (h5 : S.regs 5 = s.regs 4 - 8#64) (h14 : S.regs 14 = s.regs 14)
    (hx : S.xmm 15 = 0) (hdf : S.df = false) (hfs : S.fsBase = s.fsBase) (hmem : S.mem = proMem s z pS) :
    TopSt R R2 T b L lo hi z pS s S := by
  obtain ⟨⟨hra1, hra2, hx15, hdf0⟩, h0, h3, h1, hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hEnv0 := env_to hEnv
  have hEnv' := hEnv0
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hs64 : (s.regs 4 - 64#64).toNat = (s.regs 4).toNat - 64 := bv_sub_c _ 64 (by decide) (by omega)
  have hmf : MemFrame s.mem S.mem [(lo, hi)] := by
    rw [hmem]; unfold proMem
    repeat' first
      | exact MemFrame.refl _ _
      | refine MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  refine ⟨h4, h5, h14, hx, hdf, hfs, hmf, ?_, ?_, ?_, ?_, ?_⟩
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
  · exact Env.frame0 hMod.1 hEnv0 ⟨by rw [h4, hs64]; omega, by rw [h4, hs64]; omega, by rw [h4, hs64]; omega⟩
      (by rw [h14]) hmf (by omega)

theorem sar_and1 (m : BitVec 64) (hm : m.toNat < 2 ^ 63) :
    BitVec.setWidth 64 (BitVec.setWidth 32 ((0#64 - m).sshiftRight 63) &&& 1#32) = if m = 0#64 then 0#64 else 1#64 := by
  by_cases h0 : m = 0#64
  · subst h0; decide
  · rw [if_neg h0, sshr63_neg m (Nat.pos_of_ne_zero (fun h => h0 (BitVec.eq_of_toNat_eq (by simpa using h)))) hm]; decide

theorem sub1_lt (nS : BitVec 64) (h0 : nS.toNat ≠ 0) (h1 : nS.toNat ≤ 2 ^ 48) : (nS - 1#64).toNat = nS.toNat - 1 := by
  simp only [BitVec.toNat_sub]; simp only [Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod]; omega

def PostA (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s S : State) : Prop :=
  TopSt R R2 T b L lo hi z pS s S ∧ S.regs 0 = z ∧
    S.regs 1 = nS - BitVec.ofNat 64 (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
    ∃ k, k ≤ plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
      (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < nS.toNat → k = plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
      S.regs 3 = pS + BitVec.ofNat 64 k

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
theorem top_pro (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 sfd)
    (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (sfd + 0x3a)) s (PostA R R2 T b L lo hi z pS nS s) := by
  have hpre' := hpre
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0, h3, h1, hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hEnv0 := env_to hEnv
  have hEnv' := hEnv0
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hgl : Amd64.load s.mem ((s.regs 14).toNat + 16) 8 = .ok (s.mem.readLE ((s.regs 14).toNat + 16) 8) := by
    simp [Amd64.load, e7]
  have hacc : s.mem.accessible ((s.regs 4).toNat - 64) 88 true = true :=
    Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  have hb0 : Fv256.C.bytesAt s.mem pS.toNat 0 = s.mem.readLE pS.toNat 1 := rfl
  by_cases hn : nS = 0
  · subst hn
    have hnz : (0#64 : BitVec 64).toNat = 0 := rfl
    have hpe : plusEnd (Fv256.C.bytesAt s.mem pS.toNat) (0#64).toNat = 0 := pe_zero _ _ rfl
    janus64_run [h0, h1, h3, hacc, hnz] until [sfd + 0x3a]
    all_goals (
      refine name_state (P := PostA R R2 T b L lo hi z pS 0#64 s) ?_
      intro S2 hS2
      refine ⟨topSt_intro R R2 T b L lo hi z pS 0#64 s S2 hpre' (by simp [hS2, setRegF_apply]) (by simp [hS2, setRegF_apply])
        (by simp [hS2, setRegF_apply]) (by rw [hS2]; exact hx15) (by simp [hS2]) (by rw [hS2]) (by rw [hS2]; rfl), ?_, ?_, 0, Nat.le_refl _, fun h => absurd h (by simp), ?_⟩
      · simp [hS2, setRegF_apply, h0]
      · rw [hpe]; simp [hS2, setRegF_apply, h1]
      · simp [hS2, setRegF_apply, h3])
  · have hn' : nS.toNat ≠ 0 := fun h => hn (BitVec.eq_of_toNat_eq h)
    have hpA' : s.mem.accessible pS.toNat 1 false = true :=
      Arm64.Memory.accessible_mono _ hp (by omega) (by omega)
    have hbl := Arm64.Memory.readLE_lt s.mem pS.toNat 1
    by_cases hb : s.mem.readLE pS.toNat 1 = 43
    · have hpe : plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = 1 := pe_plus _ _ (by omega) (by rw [hb0]; exact hb)
      have hm : (nS - 1#64).toNat < 2 ^ 63 := by rw [sub1_lt nS hn' (by omega)]; omega
      janus64_run [h0, h1, h3, hacc, hn', hpA', hb, hpe] until [sfd + 0x3a]
      all_goals (
        refine name_state (P := PostA R R2 T b L lo hi z pS nS s) ?_
        intro S2 hS2
        refine ⟨topSt_intro R R2 T b L lo hi z pS nS s S2 hpre' (by simp [hS2, setRegF_apply]) (by simp [hS2, setRegF_apply])
          (by simp [hS2, setRegF_apply]) (by rw [hS2]; exact hx15) (by simp [hS2]) (by rw [hS2]) (by rw [hS2]; rfl), ?_, ?_, ?_⟩
        · simp [hS2, setRegF_apply, h0]
        · rw [hpe]; simp [hS2, setRegF_apply, h1]
        · by_cases hlt : 1 < nS.toNat
          · refine ⟨1, by omega, fun _ => hpe.symm, ?_⟩
            have hne : nS - 1#64 ≠ 0#64 := fun h => by
              have h' := congrArg BitVec.toNat h
              rw [sub1_lt nS hn' (by omega)] at h'
              simp at h'
              omega
            have hmask : BitVec.setWidth 64 (BitVec.setWidth 32 ((0#64 - (nS - 1#64)).sshiftRight 63) &&& 1#32) = 1#64 := by
              rw [sar_and1 _ hm, if_neg hne]
            rw [hS2]; simp [setRegF_apply, h3]; simpa using hmask
          · have h1' : nS = 1#64 := BitVec.eq_of_toNat_eq (by simp; omega)
            have h0' : nS - 1#64 = 0#64 := by rw [h1']; decide
            have hmask : BitVec.setWidth 64 (BitVec.setWidth 32 ((0#64 - (nS - 1#64)).sshiftRight 63) &&& 1#32) = 0#64 := by
              rw [sar_and1 _ hm, if_pos h0']
            refine ⟨0, Nat.zero_le _, fun h => absurd h (by omega), ?_⟩
            rw [hS2]; simp [setRegF_apply, h3]; simpa using hmask)
    · have hpe : plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = 0 :=
        pe_not _ _ (by rw [hb0]; omega)
      janus64_run [h0, h1, h3, hacc, hn', hpA', hb, hpe] until [sfd + 0x3a]
      all_goals (
        refine name_state (P := PostA R R2 T b L lo hi z pS nS s) ?_
        intro S2 hS2
        refine ⟨topSt_intro R R2 T b L lo hi z pS nS s S2 hpre' (by simp [hS2, setRegF_apply]) (by simp [hS2, setRegF_apply])
          (by simp [hS2, setRegF_apply]) (by rw [hS2]; exact hx15) (by simp [hS2]) (by rw [hS2]) (by rw [hS2]; rfl), ?_, ?_, 0, Nat.zero_le _, fun _ => hpe.symm, ?_⟩
        · simp [hS2, setRegF_apply, h0]
        · rw [hpe]; simp [hS2, setRegF_apply, h1]
        · simp [hS2, setRegF_apply, h3])

end Fv256.Amd64.SfdTop
