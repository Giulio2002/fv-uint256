import Fv256.Amd64.SfdTopA

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd
  Fv256.Amd64.SfdTopSpec Fv256.Amd64.SfdTopCfg Fv256.Amd64.SfdTopBr

namespace Fv256.Amd64.SfdTop

section Defs
variable (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
  (s : State)

/-- the length compare (pc `sfd + 0x57`): the number starts at `startPos`; `BX` its address, `CX` its length -/
def TopMid (S : State) : Prop :=
  TopSt R R2 T b L lo hi z pS s S ∧ S.regs 0 = z ∧
    (∃ k, k ≤ startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
      (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < nS.toNat → k = startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
      S.regs 3 = pS + BitVec.ofNat 64 k) ∧
    S.regs 1 = BitVec.ofNat 64 (nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)

/-- the zero-skip loop head (pc `sfd + 0xe0`) after `j` zero bytes -/
def LoopInv (j : Nat) (S : State) : Prop :=
  TopSt R R2 T b L lo hi z pS s S ∧ S.regs 0 = z ∧
    S.regs 3 = pS + BitVec.ofNat 64 (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
    S.regs 1 = BitVec.ofNat 64 (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
    S.regs 2 = BitVec.ofNat 64 j ∧ S.regs 6 = BitVec.ofNat 64 (j - 1) ∧
    S.mem.readLE ((s.regs 4).toNat - 24) 8 = nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
    S.mem.readLE ((s.regs 4).toNat - 16) 8 = pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
    plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < nS.toNat ∧
    j ≤ nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
    (∀ k, k < j → Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + k) = 48)

/-- the exit of the zero skip at index `i` (pc `sfd + 0x12a`) -/
def TailInv (i : Nat) (S : State) : Prop :=
  TopSt R R2 T b L lo hi z pS s S ∧ S.regs 0 = z ∧
    S.regs 3 = pS + BitVec.ofNat 64 (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
    S.regs 1 = BitVec.ofNat 64 (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
    S.regs 2 = BitVec.ofNat 64 i ∧ i < nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
    startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + i

end Defs

theorem topSt_acc {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {z pS : BitVec 64}
    {s S : State} (hS : TopSt R R2 T b L lo hi z pS s S) (a n : Nat) (w : Bool) :
    S.mem.accessible a n w = s.mem.accessible a n w := hS.2.2.2.2.2.2.1.accessible a n w

theorem topSt_byte {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {z pS nS : BitVec 64}
    {s S : State} (hS : TopSt R R2 T b L lo hi z pS s S) (hpC : nS.toNat = 0 ∨ pS.toNat + nS.toNat ≤ lo ∨ hi ≤ pS.toNat)
    (off : Nat) (h : off < nS.toNat) : S.mem.readLE (pS.toNat + off) 1 = s.mem.readLE (pS.toNat + off) 1 := by
  refine hS.2.2.2.2.2.2.1.readLE _ _ ?_
  simp only [outside_cons, outside_nil, and_true]
  omega

theorem sub_toNat (nS : BitVec 64) (pe : Nat) (hpe : pe ≤ nS.toNat) : (nS - BitVec.ofNat 64 pe).toNat = nS.toNat - pe := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := nS.isLt
  simp only [Nat.reducePow] at this ⊢
  omega

theorem sub_ofNat (nS : BitVec 64) (pe : Nat) (hpe : pe ≤ nS.toNat) :
    nS - BitVec.ofNat 64 pe = BitVec.ofNat 64 (nS.toNat - pe) := by
  apply BitVec.eq_of_toNat_eq
  rw [sub_toNat nS pe hpe, BitVec.toNat_ofNat]
  have := nS.isLt
  simp only [Nat.reducePow] at this ⊢
  omega

theorem sub_zero_eq (nS : BitVec 64) (pe : Nat) (hpe : pe ≤ nS.toNat) (h : nS - BitVec.ofNat 64 pe = 0#64) :
    nS.toNat = pe := by
  have h' := congrArg BitVec.toNat h
  rw [sub_toNat nS pe hpe] at h'
  simp at h'
  omega

theorem lt_of_sub_ne (nS : BitVec 64) (pe : Nat) (hpe : pe ≤ nS.toNat) (h : nS - BitVec.ofNat 64 pe ≠ 0#64) :
    pe < nS.toNat := by
  refine Classical.byContradiction fun hc => ?_
  have h1 : pe = nS.toNat := by omega
  apply h
  rw [h1]; simp

theorem add_toNat (p : BitVec 64) (k : Nat) (h : p.toNat + k < 2 ^ 64) : (p + BitVec.ofNat 64 k).toNat = p.toNat + k := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at h ⊢
  omega

theorem topSt_congr {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {z pS : BitVec 64}
    {s S S' : State} (h : TopSt R R2 T b L lo hi z pS s S) (h4 : S'.regs 4 = S.regs 4) (h5 : S'.regs 5 = S.regs 5)
    (h14 : S'.regs 14 = S.regs 14) (hx : S'.xmm 15 = S.xmm 15) (hdf : S'.df = S.df) (hfs : S'.fsBase = S.fsBase)
    (hm : S'.mem = S.mem) : TopSt R R2 T b L lo hi z pS s S' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  refine ⟨h4.trans a1, h5.trans a2, h14.trans a3, hx.trans a4, hdf.trans a5, hfs.trans a6, by rw [hm]; exact a7, by rw [hm]; exact a8,
    by rw [hm]; exact a9, by rw [hm]; exact a10, by rw [hm]; exact a11, ?_⟩
  unfold Fv256.Amd64.SfdEnv.Env at *
  rw [h4, h14, hm]; exact a12

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- nothing left after the `+`: straight to the length compare -/
theorem top_b0 (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (S : State) (hpc : S.rip = BitVec.ofNat 64 (sfd + 0x3a))
    (hA : PostA R R2 T b L lo hi z pS nS s S) (hz : S.regs 1 = 0#64) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (sfd + 0x57)) S (TopMid R R2 T b L lo hi z pS nS s) := by
  obtain ⟨hSt, h0, h1, k, hk1, hk2, h3⟩ := hA
  have hpe := Fv256.TopMath.plusEnd_le (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hn := sub_zero_eq nS _ hpe (h1.symm.trans hz)
  have hsp : startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = nS.toNat :=
    Fv256.TopMath.startPos_end _ _ hn.symm
  have hz' : (S.regs 1).toNat = 0 := by rw [hz]; rfl
  janus64_run [hz'] until [sfd + 0x57]
  all_goals (
    refine ⟨topSt_congr hSt rfl rfl rfl rfl rfl rfl rfl, h0, ⟨k, ?_, ?_, h3⟩, ?_⟩
    · rw [hsp]; omega
    · intro h; omega
    · show S.regs 1 = _
      rw [hsp, Nat.sub_self]; exact hz)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- the first byte of the stripped number is not `'0'`: straight to the length compare -/
theorem top_b1 (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 (sfd + 0x3a))
    (hA : PostA R R2 T b L lo hi z pS nS s S) (hR1 : S.regs 1 ≠ 0#64)
    (hbz : Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ≠ 48) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (sfd + 0x57)) S (TopMid R R2 T b L lo hi z pS nS s) := by
  obtain ⟨hSt, h0, h1, k, hk1, hk2, h3⟩ := hA
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0', h3', h1', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hpe := Fv256.TopMath.plusEnd_le (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hnS := nS.isLt
  have hlt := lt_of_sub_ne nS _ hpe (h1 ▸ hR1)
  have hk : k = plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := hk2 hlt
  subst hk
  have hr3n : (S.regs 3).toNat = pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
    rw [h3]; exact add_toNat _ _ (by simp only [Nat.reducePow]; omega)
  have hbyte : S.mem.readLE (S.regs 3).toNat 1 = Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) := by
    rw [hr3n]; exact topSt_byte hSt hpW _ hlt
  have hacc1 : S.mem.accessible (S.regs 3).toNat 1 false = true := by
    rw [topSt_acc hSt, hr3n]; exact Arm64.Memory.accessible_mono _ hp (by omega) (by omega)
  have hsp : startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat :=
    Fv256.TopMath.startPos_nz _ _ hlt hbz
  have hbne : S.mem.readLE (S.regs 3).toNat 1 ≠ 48 := by rw [hbyte]; exact hbz
  have hR1n : (S.regs 1).toNat ≠ 0 := fun h => hR1 (BitVec.eq_of_toNat_eq (by simpa using h))
  have hbne2 : ¬ S.mem.readLE (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) 1 = 48 := by rw [← hr3n]; exact hbne
  have hacc2 : S.mem.accessible (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) 1 false = true := by
    rw [← hr3n]; exact hacc1
  janus64_run [hpc, hR1n, hacc1, hbne, hacc2, hbne2] until [sfd + 0x57]
  all_goals (
    refine ⟨topSt_congr hSt rfl rfl rfl rfl rfl rfl rfl, ?_, ⟨_, Nat.le_refl _, fun _ => rfl, ?_⟩, ?_⟩
    · simp [h0]
    · rw [hsp]; simp [h3]
    · simp [h1, hsp, sub_ofNat nS _ hpe])

theorem r2_eq (m i : Nat) (h : i ≤ m) (hm : m < 2 ^ 64) : BitVec.ofNat 64 m - BitVec.ofNat 64 i = BitVec.ofNat 64 (m - i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at hm ⊢
  omega

theorem topSt_wr {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {z pS : BitVec 64}
    {s S S' : State} (hL : R2.Laws) (hS : TopSt R R2 T b L lo hi z pS s S) (hlo : 64 ≤ (s.regs 4).toNat)
    (h4 : S'.regs 4 = S.regs 4) (h5 : S'.regs 5 = S.regs 5) (h14 : S'.regs 14 = S.regs 14) (hx : S'.xmm 15 = S.xmm 15)
    (hdf : S'.df = S.df) (hfs : S'.fsBase = S.fsBase) (hf : MemFrame S.mem S'.mem [(lo, hi)]) (hw : lo + 32 ≤ hi)
    (e1 : S'.mem.readLE ((s.regs 4).toNat - 8) 8 = S.mem.readLE ((s.regs 4).toNat - 8) 8)
    (e2 : S'.mem.readLE ((s.regs 4).toNat + 8) 8 = S.mem.readLE ((s.regs 4).toNat + 8) 8)
    (e3 : S'.mem.readLE ((s.regs 4).toNat + 16) 8 = S.mem.readLE ((s.regs 4).toNat + 16) 8)
    (e4 : S'.mem.readLE (s.regs 4).toNat 8 = S.mem.readLE (s.regs 4).toNat 8) :
    TopSt R R2 T b L lo hi z pS s S' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hS
  have hEnv := a12
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18⟩ := a12
  refine ⟨h4.trans a1, h5.trans a2, h14.trans a3, hx.trans a4, hdf.trans a5, hfs.trans a6, ?_, e1.trans a8, e2.trans a9, e3.trans a10,
    e4.trans a11, ?_⟩
  · exact MemFrame.trans a7 hf (fun a n h => ⟨h, h⟩)
  · exact Env.frame0 hL hEnv ⟨by rw [h4]; exact c1, by rw [h4]; exact c2, by rw [h4]; exact c4⟩ h14 hf hw

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- the first byte of the stripped number is `'0'`: spill and enter the zero-skip loop -/
theorem top_b2 (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 (sfd + 0x3a))
    (hA : PostA R R2 T b L lo hi z pS nS s S) (hR1 : S.regs 1 ≠ 0#64)
    (hbz : Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) = 48) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (sfd + 0xe0)) S (LoopInv R R2 T b L lo hi z pS nS s 0) := by
  obtain ⟨hSt, h0, h1, k, hk1, hk2, h3⟩ := hA
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0', h3', h1', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hEnv0 := env_to hEnv
  have hEnv' := hEnv0
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hpe := Fv256.TopMath.plusEnd_le (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hnS := nS.isLt
  have hlt := lt_of_sub_ne nS _ hpe (h1 ▸ hR1)
  have hk : k = plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := hk2 hlt
  subst hk
  have hr3n : (S.regs 3).toNat = pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
    rw [h3]; exact add_toNat _ _ (by simp only [Nat.reducePow]; omega)
  have hbyte : S.mem.readLE (S.regs 3).toNat 1 = Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) := by
    rw [hr3n]; exact topSt_byte hSt hpW _ hlt
  have hacc1 : S.mem.accessible (S.regs 3).toNat 1 false = true := by
    rw [topSt_acc hSt, hr3n]; exact Arm64.Memory.accessible_mono _ hp (by omega) (by omega)
  have hbeq : S.mem.readLE (S.regs 3).toNat 1 = 48 := by rw [hbyte]; exact hbz
  have hR1n : (S.regs 1).toNat ≠ 0 := fun h => hR1 (BitVec.eq_of_toNat_eq (by simpa using h))
  have hbeq2 : S.mem.readLE (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) 1 = 48 := by rw [← hr3n]; exact hbeq
  have hacc2 : S.mem.accessible (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) 1 false = true := by
    rw [← hr3n]; exact hacc1
  have hwacc : S.mem.accessible ((s.regs 4).toNat - 24) 16 true = true := by
    rw [topSt_acc hSt]; exact Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 64 := by rw [hSt.1]; exact bv_sub_c _ 64 (by decide) (by omega)
  janus64_run [hpc, hR1n, hacc1, hbeq, hacc2, hbeq2, hwacc, hS4] until [sfd + 0xe0]
  all_goals (
    refine name_state (P := LoopInv R R2 T b L lo hi z pS nS s 0) ?_
    intro S2 hS2
    have hm2 : S2.mem = (S.mem.writeLE ((s.regs 4).toNat - 24) 8 (2 ^ 64 - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + nS.toNat)).writeLE
        ((s.regs 4).toNat - 16) 8 (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) := by
      rw [hS2]; dsimp only
      have e1 : (s.regs 4).toNat - 64 + 40 = (s.regs 4).toNat - 24 := by omega
      have e2 : (s.regs 4).toNat - 64 + 48 = (s.regs 4).toNat - 16 := by omega
      rw [e1, e2]
    have hmf : MemFrame S.mem S2.mem [(lo, hi)] := by
      rw [hm2]
      repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
    have hg : ∀ (k : Nat), S2.regs k = (setRegF (setRegF S.regs 2 0#64) 6 0#64) k := by intro k; rw [hS2]
    refine ⟨topSt_wr hMod.1 hSt (by omega) ?_ ?_ ?_ ?_ ?_ ?_ hmf (by omega) ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlt, Nat.zero_le _, fun k hk => absurd hk (by omega)⟩
    · rw [hg 4]; simp [setRegF_apply]
    · rw [hg 5]; simp [setRegF_apply]
    · rw [hg 14]; simp [setRegF_apply]
    · rw [hS2]
    · rw [hS2]
    · rw [hS2]
    · rw [hm2]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    · rw [hm2]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    · rw [hm2]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    · rw [hm2]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    · rw [hg 0]; simp [setRegF_apply, h0]
    · rw [hg 3]; simp [setRegF_apply, h3]
    · rw [hg 1]; simp [setRegF_apply, h1, sub_ofNat nS _ hpe]
    · rw [hg 2]; simp [setRegF_apply]
    · rw [hg 6]; simp [setRegF_apply]
    · rw [hm2]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; omega
    · rw [hm2]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (by omega))


set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- `s = s[i:]` and back to the length compare -/
theorem top_tail (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre extCfg R R2 T b L lo hi z pS nS s)
    (S : State) (i : Nat) (hpc : S.rip = BitVec.ofNat 64 (sfd + 0x12a))
    (hT : TailInv R R2 T b L lo hi z pS nS s i S) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (sfd + 0x57)) S (TopMid R R2 T b L lo hi z pS nS s) := by
  obtain ⟨hSt, h0, h3, h1, h2, hi1, hsp⟩ := hT
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0', h3', h1', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hpre
  have hnS := nS.isLt
  have hpe := Fv256.TopMath.plusEnd_le (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hmm : nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < 2 ^ 64 := by omega
  have hsub : (BitVec.ofNat 64 (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) - BitVec.ofNat 64 i).toNat =
      nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat - i := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; simp only [Nat.reducePow]; omega
  have hmask : (0#64 - (BitVec.ofNat 64 (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) - BitVec.ofNat 64 i)).sshiftRight 63 &&&
      BitVec.ofNat 64 i = BitVec.ofNat 64 i := by
    rw [sshr63_neg _ (by rw [hsub]; omega) (by rw [hsub]; omega)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_allOnes, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (BitVec.isLt _)]
  janus64_run [hpc, h1, h2, h3, hmask] until [sfd + 0x57]
  all_goals (
    refine name_state (P := TopMid R R2 T b L lo hi z pS nS s) ?_
    intro S2 hS2
    refine ⟨topSt_congr hSt (by simp [hS2, setRegF_apply]) (by simp [hS2, setRegF_apply]) (by simp [hS2, setRegF_apply])
      (by rw [hS2]) (by rw [hS2]) (by rw [hS2]) (by rw [hS2]), ?_, ⟨plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + i, ?_, ?_, ?_⟩, ?_⟩
    · simp [hS2, setRegF_apply, h0]
    · rw [hsp]; omega
    · intro _; rw [hsp]
    · simp only [hS2, setRegF_apply]; simp [hmask, BitVec.ofNat_add]
    · simp only [hS2, setRegF_apply]; simp
      rw [r2_eq _ _ (by omega) hmm, hsp]; congr 1; omega)

end Fv256.Amd64.SfdTop
