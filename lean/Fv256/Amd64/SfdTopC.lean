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
    (ihn : ∀ S', S'.rip = BitVec.ofNat 64 (sfd + 0xe0) → LoopInv R R2 T b L lo hi z pS nS s (j + 1) S' → ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (BitVec.ofNat 64 (sfd + 0x12a)) S' Q) :
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (BitVec.ofNat 64 (sfd + 0x12a)) S Q := by
  obtain ⟨hSt, h0, h3, h1, h2, h6, m1, m2, hlt, hjle, hzs⟩ := hI
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0', h3', h1', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hnS := nS.isLt
  have hpe := Fv256.TopMath.plusEnd_le (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hjI := ofNat_toInt j (by omega)
  have hmI := ofNat_toInt (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (by omega)
  have hacc3 : S.mem.accessible (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 false = true := by
    rw [topSt_acc hSt]; exact Arm64.Memory.accessible_mono _ (hp.resolve_left (by omega)) (by omega) (by omega)
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
    refine ihn _ (by first | rfl | decide | simp [sfd]) ?_
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

theorem jg_not_taken : ∀ x : Fin 256, x.val ≤ 127 →
    ¬ (¬ BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 x.val))) - 127#32 = 0#32 ∧
      ((BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 x.val))) - 127#32).msb !=
        !decide ((BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 x.val))) - 127#32).toInt =
          (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 x.val)))).toInt - 127 - 0)) = false) := by
  decide +kernel

theorem je_not : ∀ x : Fin 256, x.val ≠ 48 →
    ¬ (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 x.val))) - 48#32 = 0#32) := by
  decide +kernel

theorem jg_taken : ∀ x : Fin 256, 127 < x.val →
    (¬ BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 x.val))) - 127#32 = 0#32 ∧
      ((BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 x.val))) - 127#32).msb !=
        !decide ((BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 x.val))) - 127#32).toInt =
          (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 x.val)))).toInt - 127 - 0)) = false) := by
  decide +kernel

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- a non-zero ASCII byte ends the zero run -/
theorem top_lb (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (S : State) (j : Nat) (hpc : S.rip = BitVec.ofNat 64 (sfd + 0xe0))
    (hI : LoopInv R R2 T b L lo hi z pS nS s j S) (hjm : j + 1 ≤ nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)
    (hb127 : Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) ≤ 127)
    (hb48 : Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) ≠ 48) :
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (BitVec.ofNat 64 (sfd + 0x12a)) S (TailInv R R2 T b L lo hi z pS nS s j) := by
  obtain ⟨hSt, h0, h3, h1, h2, h6, m1, m2, hlt, hjle, hzs⟩ := hI
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0', h3', h1', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hnS := nS.isLt
  have hpe := Fv256.TopMath.plusEnd_le (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hjI := ofNat_toInt j (by omega)
  have hmI := ofNat_toInt (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (by omega)
  have hacc3 : S.mem.accessible (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 false = true := by
    rw [topSt_acc hSt]; exact Arm64.Memory.accessible_mono _ (hp.resolve_left (by omega)) (by omega) (by omega)
  have hbyte3 : S.mem.readLE (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 =
      Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) := by
    rw [topSt_byte hSt hpW _ (by omega)]; rfl
  have hacc4 : S.mem.accessible (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) 1 false = true := by
    rw [Nat.add_assoc]; exact hacc3
  have hbyte4 : S.mem.readLE (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) 1 =
      Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) := by
    rw [Nat.add_assoc]; exact hbyte3
  have hx48 : ¬ S.mem.readLE (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 = 48 := by
    rw [hbyte3]; exact hb48
  have hx127 : S.mem.readLE (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 ≤ 127 := by
    rw [hbyte3]; exact hb127
  have hbl : Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) < 256 := by
    have := Arm64.Memory.readLE_lt s.mem (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1
    simpa [Fv256.C.bytesAt] using this
  have hJ := jg_not_taken ⟨_, hbl⟩ hb127
  have hJe := je_not ⟨_, hbl⟩ hb48
  janus64_run [hpc, h1, h2, h3, hjI, hmI, hacc3, hbyte3, hacc4, hbyte4, hx48, hx127, hJ, hJe] until [sfd + 0x12a]
  all_goals (
    refine name_state (P := TailInv R R2 T b L lo hi z pS nS s j) ?_
    intro S2 hS2
    refine ⟨topSt_congr hSt (by simp [hS2, setRegF_apply]) (by simp [hS2, setRegF_apply]) (by simp [hS2, setRegF_apply])
      (by rw [hS2]) (by rw [hS2]) (by rw [hS2]) (by rw [hS2]), ?_, ?_, ?_, ?_, by omega, Fv256.TopMath.startPos_a _ _ _ (by omega) hb48 hzs⟩
    · simp [hS2, setRegF_apply, h0]
    · simp [hS2, setRegF_apply, h3]
    · simp [hS2, setRegF_apply, h1]
    · simp [hS2, setRegF_apply, h2])

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- the whole stripped number is zeros: keep the last `'0'` -/
theorem top_lend (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (S : State) (j : Nat) (hpc : S.rip = BitVec.ofNat 64 (sfd + 0xe0))
    (hI : LoopInv R R2 T b L lo hi z pS nS s j S) (hjm : nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ≤ j) :
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (BitVec.ofNat 64 (sfd + 0x12a)) S
      (TailInv R R2 T b L lo hi z pS nS s (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat - 1)) := by
  obtain ⟨hSt, h0, h3, h1, h2, h6, m1, m2, hlt, hjle, hzs⟩ := hI
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0', h3', h1', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hnS := nS.isLt
  have hpe := Fv256.TopMath.plusEnd_le (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hjeq : j = nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by omega
  have hjI := ofNat_toInt j (by omega)
  have hmI := ofNat_toInt (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (by omega)
  have hsp : startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = nS.toNat - 1 :=
    Fv256.TopMath.startPos_b _ _ hlt (fun k hk1 hk2 => by
      have := hzs (k - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (by omega)
      rwa [show plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + (k - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) = k by omega] at this)
  janus64_run [hpc, h1, h2, h3, h6, hjI, hmI] until [sfd + 0x12a]
  all_goals (
    refine name_state (P := TailInv R R2 T b L lo hi z pS nS s (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat - 1)) ?_
    intro S2 hS2
    refine ⟨topSt_congr hSt (by simp [hS2, setRegF_apply]) (by simp [hS2, setRegF_apply]) (by simp [hS2, setRegF_apply])
      (by rw [hS2]) (by rw [hS2]) (by rw [hS2]) (by rw [hS2]), ?_, ?_, ?_, ?_, by omega, by omega⟩
    · simp [hS2, setRegF_apply, h0]
    · simp [hS2, setRegF_apply, h3]
    · simp [hS2, setRegF_apply, h1]
    · simp [hS2, setRegF_apply]; congr 1; omega)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- a byte `>= 0x80` (`runtime.decoderune`): the decoded rune is never `'0'` -/
theorem top_ld (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (S : State) (j : Nat) (hpc : S.rip = BitVec.ofNat 64 (sfd + 0xe0))
    (hI : LoopInv R R2 T b L lo hi z pS nS s j S) (hjm : j + 1 ≤ nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)
    (hb128 : 127 < Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) :
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (BitVec.ofNat 64 (sfd + 0x12a)) S (TailInv R R2 T b L lo hi z pS nS s j) := by
  obtain ⟨hSt, h0, h3, h1, h2, h6, m1, m2, hlt, hjle, hzs⟩ := hI
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0', h3', h1', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hEnv0 := env_to hEnv
  have hEnv' := hEnv0
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hnS := nS.isLt
  have hpe := Fv256.TopMath.plusEnd_le (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hjI := ofNat_toInt j (by omega)
  have hmI := ofNat_toInt (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (by omega)
  have hacc3 : S.mem.accessible (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 false = true := by
    rw [topSt_acc hSt]; exact Arm64.Memory.accessible_mono _ (hp.resolve_left (by omega)) (by omega) (by omega)
  have hbyte3 : S.mem.readLE (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 =
      Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) := by
    rw [topSt_byte hSt hpW _ (by omega)]; rfl
  have hacc4 : S.mem.accessible (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) 1 false = true := by
    rw [Nat.add_assoc]; exact hacc3
  have hbyte4 : S.mem.readLE (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) 1 =
      Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) := by
    rw [Nat.add_assoc]; exact hbyte3
  have hbl : Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) < 256 := by
    have := Arm64.Memory.readLE_lt s.mem (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1
    simpa [Fv256.C.bytesAt] using this
  have hJ := jg_taken ⟨_, hbl⟩ hb128
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 64 := by rw [hSt.1]; exact bv_sub_c _ 64 (by decide) (by omega)
  janus64_run [hpc, h1, h2, h3, hjI, hmI, hacc3, hbyte3, hacc4, hbyte4, hJ, hS4] until [Fv256.Amd64.SfdDecode.dr]
  have hpe1 : (pS + BitVec.ofNat 64 (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)).toNat = pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat :=
    add_toNat _ _ (by simp only [Nat.reducePow]; omega)
  have hlen1 : (BitVec.ofNat 64 (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)).toNat = nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hk1 : (BitVec.ofNat 64 j).toNat = j := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  all_goals (
    refine reach_name ?_
    intro S1 hS1
    have hm1 : S1.mem = (S.mem.writeLE ((s.regs 4).toNat - 32) 8 j).writeLE ((s.regs 4).toNat - 72) 8 4933415 := by
      rw [hS1]; dsimp only
      have e1 : (s.regs 4).toNat - 64 + 32 = (s.regs 4).toNat - 32 := by omega
      have e2 : (s.regs 4).toNat - 64 - 8 = (s.regs 4).toNat - 72 := by omega
      rw [e1, e2]
    have hg4 : S1.regs 4 = s.regs 4 - 72#64 := by
      rw [hS1]; simp only [setRegF_apply]; simp [hSt.1]; bv_omega
    have hs1 : (S1.regs 4).toNat = (s.regs 4).toNat - 72 := by rw [hg4]; exact bv_sub_c _ 72 (by decide) (by omega)
    have hmf1 : MemFrame S.mem S1.mem [(lo, hi)] := by
      rw [hm1]
      repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
    have hr0 : S1.regs 0 = pS + BitVec.ofNat 64 (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) := by rw [hS1]; simp [setRegF_apply]
    have hr3 : S1.regs 3 = BitVec.ofNat 64 (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) := by rw [hS1]; simp [setRegF_apply]
    have hr1 : S1.regs 1 = BitVec.ofNat 64 j := by rw [hS1]; simp [setRegF_apply]
    have hret : S1.mem.readLE (S1.regs 4).toNat 8 = 4933415 := by
      rw [hs1, hm1]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
      all_goals (try (rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (by decide)))
    refine ReachesRet.call (Fv256.Amd64.SfdDecode.decoderune_sum impl (pS + BitVec.ofNat 64 (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat))
      (BitVec.ofNat 64 j) (BitVec.ofNat 64 (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat))) (by rw [hS1]; rfl) ?_ ?_
    · have hpW' : pS.toNat + nS.toNat ≤ lo ∨ hi ≤ pS.toNat := hpW.resolve_left (by omega)
      refine ⟨⟨?_, ?_, ?_, ?_⟩, hr0, hr3, hr1, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · rw [hmf1.accessible, topSt_acc hSt, hs1]
        exact Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ e5 (by omega) (by omega))
      · rw [hret]; decide
      · rw [hS1]; exact hSt.2.2.2.1
      · rw [hS1]; exact hSt.2.2.2.2.1
      · rw [hpe1, hlen1]; omega
      · rw [hmf1.accessible, topSt_acc hSt, hpe1, hlen1]
        exact Arm64.Memory.accessible_mono _ (hp.resolve_left (by omega)) (by omega) (by omega)
      · rw [hk1, hlen1]; omega
      · try simp only [regSP]
        refine ⟨by rw [hs1]; omega, by rw [hs1]; omega, ?_⟩
        rw [hmf1.accessible, topSt_acc hSt, hs1]
        exact Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
      · try simp only [regSP]
        rw [hs1, hpe1, hlen1]; omega
    · intro S' hpc' ⟨k1, k2, k3, k4, k5, k6, k7, h128, h32, hfr⟩
      have hSt' := hSt
      obtain ⟨t4, t5, t14, tx, tdf, tfs, tmf, tbp, tz, tp, tret, tenv⟩ := hSt'
      have hS'4 : S'.regs 4 = s.regs 4 - 64#64 := by rw [k2, hg4]; bv_omega
      have hS'4n : (S'.regs 4).toNat = (s.regs 4).toNat - 64 := by rw [hS'4]; exact bv_sub_c _ 64 (by decide) (by omega)
      have hfr' : MemFrame S1.mem S'.mem [((s.regs 4).toNat - 80, (s.regs 4).toNat - 72), ((s.regs 4).toNat - 64, (s.regs 4).toNat - 56)] := by
        have := hfr; rw [hs1] at this
        exact this.mono (by intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
      have hmfS : MemFrame S.mem S'.mem [(lo, hi)] := by
        have h2 : MemFrame S1.mem S'.mem [(lo, hi)] := hfr'.mono (by intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
        exact MemFrame.trans hmf1 h2 (fun a n h => ⟨h, h⟩)
      have hrd : ∀ a, (a + 8 ≤ (s.regs 4).toNat - 80 ∨ (s.regs 4).toNat - 72 ≤ a) → (a + 8 ≤ (s.regs 4).toNat - 64 ∨ (s.regs 4).toNat - 56 ≤ a) →
          S'.mem.readLE a 8 = S1.mem.readLE a 8 := fun a h1 h2 =>
        hfr'.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
      have hCX : S'.mem.readLE ((s.regs 4).toNat - 64 + 40) 8 = nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
        rw [hrd _ (by omega) (by omega), hm1]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        have : (s.regs 4).toNat - 64 + 40 = (s.regs 4).toNat - 24 := by omega
        rw [this]; exact m1
      have hBX : S'.mem.readLE ((s.regs 4).toNat - 64 + 48) 8 = pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
        rw [hrd _ (by omega) (by omega), hm1]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        have : (s.regs 4).toNat - 64 + 48 = (s.regs 4).toNat - 16 := by omega
        rw [this]; exact m2
      have hDX : S'.mem.readLE ((s.regs 4).toNat - 64 + 32) 8 = j := by
        rw [hrd _ (by omega) (by omega), hm1]
        have : (s.regs 4).toNat - 64 + 32 = (s.regs 4).toNat - 32 := by omega
        rw [this]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (by omega)
      have hAX : S'.mem.readLE ((s.regs 4).toNat - 64 + 72) 8 = z.toNat := by
        rw [hrd _ (by omega) (by omega), hm1]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        have : (s.regs 4).toNat - 64 + 72 = (s.regs 4).toNat + 8 := by omega
        rw [this]; exact tz
      have haccS' : ∀ a n, lo ≤ a → a + n ≤ hi → S'.mem.accessible a n false = true := by
        intro a n h1 h2
        rw [hmfS.accessible, topSt_acc hSt]
        exact Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ e5 (by omega) (by omega))
      have hne : ¬ (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (S'.regs 0))) - 48#32 = 0#32) := by
        intro h
        have h' := congrArg BitVec.toNat h
        simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h'
        simp only [Nat.reducePow] at h'
        omega
      have hcx : S'.mem.accessible ((s.regs 4).toNat - 64 + 40) 8 false = true := haccS' _ _ (by omega) (by omega)
      have hbx : S'.mem.accessible ((s.regs 4).toNat - 64 + 48) 8 false = true := haccS' _ _ (by omega) (by omega)
      have hdx : S'.mem.accessible ((s.regs 4).toNat - 64 + 32) 8 false = true := haccS' _ _ (by omega) (by omega)
      have hax : S'.mem.accessible ((s.regs 4).toNat - 64 + 72) 8 false = true := haccS' _ _ (by omega) (by omega)
      janus64_run [hS'4, hS'4n, hCX, hBX, hDX, hAX, hcx, hbx, hdx, hax, hne] until [sfd + 0x12a]
      all_goals (
        refine name_state (P := TailInv R R2 T b L lo hi z pS nS s j) ?_
        intro S2 hS2
        have e5' : S1.regs 5 = S.regs 5 := by rw [hS1]; simp [setRegF_apply]
        have e14' : S1.regs 14 = S.regs 14 := by rw [hS1]; simp [setRegF_apply]
        have ex' : S1.xmm 15 = S.xmm 15 := by rw [hS1]
        have edf' : S1.df = S.df := by rw [hS1]
        have efs' : S1.fsBase = S.fsBase := by rw [hS1]
        have hrd0 : ∀ a, (a + 8 ≤ (s.regs 4).toNat - 80 ∨ (s.regs 4).toNat - 72 ≤ a) → (a + 8 ≤ (s.regs 4).toNat - 64 ∨ (s.regs 4).toNat - 56 ≤ a) →
            (a + 8 ≤ (s.regs 4).toNat - 32 ∨ (s.regs 4).toNat - 24 ≤ a) → (a + 8 ≤ (s.regs 4).toNat - 72 ∨ (s.regs 4).toNat - 64 ≤ a) →
            S'.mem.readLE a 8 = S.mem.readLE a 8 := by
          intro a h1 h2 h3 h4
          rw [hrd a h1 h2, hm1]
          simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        refine ⟨topSt_wr hMod.1 hSt (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by omega) ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_, by omega,
          Fv256.TopMath.startPos_a _ _ _ (by omega) (by omega) hzs⟩
        · simp only [hS2, setRegF_apply]; simp; rw [hS'4, hSt.1]
        · simp only [hS2, setRegF_apply]; simp; rw [k3, e5']
        · simp only [hS2, setRegF_apply]; simp; rw [k4, e14']
        · rw [hS2]; simp; rw [k5, ex']
        · rw [hS2]; simp; rw [edf']
        · rw [hS2]; simp; rw [k7, efs']
        · rw [hS2]; exact hmfS
        · rw [hS2]; exact hrd0 _ (by omega) (by omega) (by omega) (by omega)
        · rw [hS2]; exact hrd0 _ (by omega) (by omega) (by omega) (by omega)
        · rw [hS2]; exact hrd0 _ (by omega) (by omega) (by omega) (by omega)
        · rw [hS2]; exact hrd0 _ (by omega) (by omega) (by omega) (by omega)
        · simp [hS2, setRegF_apply]
        · simp only [hS2, setRegF_apply]; simp; rw [← hpe1]; exact (bvo _).symm
        · simp [hS2, setRegF_apply]
        · simp [hS2, setRegF_apply]))

end Fv256.Amd64.SfdTop
