import Fv256.Amd64.SfdTopB

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd
  Fv256.Amd64.SfdTopSpec Fv256.Amd64.SfdTopCfg Fv256.Amd64.SfdTopBr

namespace Fv256.Amd64.SfdTop

theorem ofNat_toInt (n : Nat) (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).toInt = (n : Int) := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
  simp only [Nat.reducePow]
  split <;> omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- one more zero byte: back to the loop head -/
theorem top_ls (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (S : State) (j : Nat) (hpc : S.rip = BitVec.ofNat 64 (sfd + 0xe0))
    (hI : LoopInv R R2 T b L lo hi z pS nS s j S) (hjm : j + 1 ≤ nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)
    (hbz : Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) = 48)
    {Q : State → Prop}
    (ihn : ∀ S', LoopInv R R2 T b L lo hi z pS nS s (j + 1) S' → ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (sfd + 0x12a)) S' Q) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (sfd + 0x12a)) S Q := by
  obtain ⟨hSt, h0, h3, h1, h2, h6, m1, m2, hlt, hjle, hzs⟩ := hI
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0', h3', h1', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hnS := nS.isLt
  have hpe := Fv256.TopMath.plusEnd_le (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hjI := ofNat_toInt j (by omega)
  have hmI := ofNat_toInt (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (by omega)
  have hacc3 : S.mem.accessible (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 false = true := by
    rw [topSt_acc hSt]; exact Arm64.Memory.accessible_mono _ hp (by omega) (by omega)
  have hbyte3 : S.mem.readLE (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 = 48 := by
    rw [topSt_byte hSt hpW _ (by omega)]; exact hbz
  have hacc4 : S.mem.accessible (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) 1 false = true := by
    rw [Nat.add_assoc]; exact hacc3
  have hbyte4 : S.mem.readLE (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) 1 = 48 := by
    rw [Nat.add_assoc]; exact hbyte3
  janus64_step [hpc, h1, h2, h3, hjI, hmI, hacc3, hbyte3, hacc4, hbyte4]
  have hmsb : ¬ (4294967217#32).msb = false := by decide
  janus64_run [h1, h2, h3, hjI, hmI, hacc3, hbyte3, hacc4, hbyte4, hmsb] until [sfd + 0xe0]
  all_goals (
    refine ihn _ ?_
    refine ⟨topSt_congr hSt rfl rfl rfl rfl rfl rfl rfl, ?_, ?_, ?_, ?_, ?_, m1, m2, hlt, hjm, ?_⟩
    · simp [setRegF_apply, h0]
    · simp [setRegF_apply, h3]
    · simp [setRegF_apply, h1]
    · simp [setRegF_apply]
    · simp [setRegF_apply]
    · intro k hk
      by_cases hkj : k < j
      · exact hzs k hkj
      · have : k = j := by omega
        subst this; exact hbz)

end Fv256.Amd64.SfdTop
