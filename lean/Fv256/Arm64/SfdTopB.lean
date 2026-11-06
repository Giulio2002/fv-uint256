import Fv256.Arm64.SfdTopA

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdTopSpec

namespace Fv256.Arm64.SfdTop

section Defs
variable (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
  (s : State)

/-- after the `+` skip (pc `0xb89f4`) -/
def PostA (S : State) : Prop :=
  TopSt R R2 T b L lo hi z pS s S ∧ S.regs 0 = z ∧
    S.regs 2 = nS - BitVec.ofNat 64 (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
    ∃ k, k ≤ plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
      (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < nS.toNat → k = plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
      S.regs 1 = pS + BitVec.ofNat 64 k

/-- the number starts at `startPos` (pc `0xb8a18`): `R1` its address, `R2` its length -/
def TopMid (S : State) : Prop :=
  TopSt R R2 T b L lo hi z pS s S ∧ S.regs 0 = z ∧
    (∃ k, k ≤ startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
      (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < nS.toNat → k = startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
      S.regs 1 = pS + BitVec.ofNat 64 k) ∧
    S.regs 2 = BitVec.ofNat 64 (nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)

/-- the zero-skip loop head (pc `0xb8ab0`) after `j` zero bytes -/
def LoopInv (j : Nat) (S : State) : Prop :=
  TopSt R R2 T b L lo hi z pS s S ∧ S.regs 0 = z ∧
    S.regs 1 = pS + BitVec.ofNat 64 (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
    S.regs 2 = BitVec.ofNat 64 (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
    S.regs 3 = BitVec.ofNat 64 j ∧ S.regs 4 = BitVec.ofNat 64 (j - 1) ∧
    S.mem.readLE (s.sp.toNat - 24) 8 = nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
    S.mem.readLE (s.sp.toNat - 16) 8 = pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
    plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < nS.toNat ∧
    j ≤ nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
    (∀ k, k < j → Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + k) = 48)

end Defs

theorem topSt_acc {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {z pS : BitVec 64}
    {s S : State} (hS : TopSt R R2 T b L lo hi z pS s S) (a n : Nat) (w : Bool) :
    S.mem.accessible a n w = s.mem.accessible a n w := hS.2.2.2.2.1.accessible a n w

theorem topSt_byte {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {z pS nS : BitVec 64}
    {s S : State} (hS : TopSt R R2 T b L lo hi z pS s S) (hpC : pS.toNat + nS.toNat ≤ lo ∨ hi ≤ pS.toNat)
    (off : Nat) (h : off < nS.toNat) : S.mem.readLE (pS.toNat + off) 1 = s.mem.readLE (pS.toNat + off) 1 := by
  refine hS.2.2.2.2.1.readLE _ _ ?_
  simp only [outside_cons, outside_nil, and_true]
  omega

theorem sub_zero_eq (nS : BitVec 64) (pe : Nat) (hpe : pe ≤ nS.toNat) (h : nS - BitVec.ofNat 64 pe = 0#64) :
    nS.toNat = pe := by
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h'
  have := nS.isLt
  simp only [Nat.reducePow] at this h'
  omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- nothing left after the `+`: straight to the length compare -/
theorem top_b0 (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (S : State) (hpc : S.pc = BitVec.ofNat 64 0xb89f4)
    (hA : PostA R R2 T b L lo hi z pS nS s S) (hz : S.regs 2 = 0#64) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (BitVec.ofNat 64 0xb8a18) S
      (TopMid R R2 T b L lo hi z pS nS s) := by
  obtain ⟨hSt, h0, h2, k, hk1, hk2, h1⟩ := hA
  have hpe := Fv256.TopMath.plusEnd_le (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hn := sub_zero_eq nS _ hpe (h2.symm.trans hz)
  have hsp : startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = nS.toNat :=
    Fv256.TopMath.startPos_end _ _ hn.symm
  janus_run [hpc, hz] until [0xb8a18]
  all_goals (
    refine ⟨hSt, h0, ⟨k, ?_, ?_, h1⟩, ?_⟩
    · rw [hsp]; omega
    · intro h; omega
    · show S.regs 2 = _
      rw [hsp, Nat.sub_self]; exact hz)

theorem topSt_sp {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {z pS : BitVec 64}
    {s S : State} (hS : TopSt R R2 T b L lo hi z pS s S) (h : 80 ≤ s.sp.toNat) :
    S.sp.toNat = s.sp.toNat - 80 := by
  rw [hS.1]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := s.sp.isLt; simp only [Nat.reducePow] at this; omega

/-- `TopSt` survives a step that only writes the window and keeps the six words that matter -/
theorem topSt_step {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {z pS : BitVec 64}
    {s S S' : State} (hL : R2.Laws) (hS : TopSt R R2 T b L lo hi z pS s S) (hlo : 80 ≤ s.sp.toNat)
    (hsp : S'.sp = S.sp) (h29 : S'.regs 29 = S.regs 29) (h28 : S'.regs 28 = S.regs 28)
    (h18 : S'.regs 18 = S.regs 18) (hf : MemFrame S.mem S'.mem [(lo, hi)]) (hw : lo + 32 ≤ hi)
    (e1 : S'.mem.readLE (s.sp.toNat - 80) 8 = S.mem.readLE (s.sp.toNat - 80) 8)
    (e2 : S'.mem.readLE (s.sp.toNat - 88) 8 = S.mem.readLE (s.sp.toNat - 88) 8)
    (e3 : S'.mem.readLE (s.sp.toNat + 8) 8 = S.mem.readLE (s.sp.toNat + 8) 8)
    (e4 : S'.mem.readLE (s.sp.toNat + 16) 8 = S.mem.readLE (s.sp.toNat + 16) 8)
    (e5 : S'.mem.readLE (s.sp.toNat - 8) 8 = S.mem.readLE (s.sp.toNat - 8) 8)
    (e6 : S'.mem.readLE s.sp.toNat 8 = S.mem.readLE s.sp.toNat 8) :
    TopSt R R2 T b L lo hi z pS s S' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hS
  have hEnv := a12
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18⟩ := a12
  refine ⟨hsp.trans a1, h29.trans a2, h28.trans a3, h18.trans a4, ?_, e1.trans a6, e2.trans a7, e3.trans a8,
    e4.trans a9, e5.trans a10, e6.trans a11, ?_⟩
  · exact MemFrame.trans a5 hf (fun a n h => ⟨h, h⟩)
  · exact Fv256.Arm64.SfdEnv.Env.frame0 hL hEnv ⟨by rw [hsp]; exact c1, by rw [hsp]; exact c2, by rw [hsp]; exact c4⟩
      h28 hf hw

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

theorem lt_of_sub_ne (nS : BitVec 64) (pe : Nat) (hpe : pe ≤ nS.toNat) (h : nS - BitVec.ofNat 64 pe ≠ 0#64) :
    pe < nS.toNat := by
  refine Classical.byContradiction fun hc => ?_
  have h1 : pe = nS.toNat := by omega
  apply h
  rw [h1]; simp

theorem byte_eqc (x c : Nat) (hx : x < 256) (hc : c < 256) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 x)).toNat = c ↔ x = c := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem add_toNat (p : BitVec 64) (k : Nat) (h : p.toNat + k < 2 ^ 64) : (p + BitVec.ofNat 64 k).toNat = p.toNat + k := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at h ⊢
  omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- the first byte of the stripped number is not `'0'`: straight to the length compare -/
theorem top_b1 (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 0xb89f4)
    (hA : PostA R R2 T b L lo hi z pS nS s S) (hR2 : S.regs 2 ≠ 0#64)
    (hbz : Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ≠ 48) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (BitVec.ofNat 64 0xb8a18) S
      (TopMid R R2 T b L lo hi z pS nS s) := by
  obtain ⟨hSt, h0, h2, k, hk1, hk2, h1⟩ := hA
  obtain ⟨hl1, hl2, h0', h1', h2', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  have hpe := Fv256.TopMath.plusEnd_le (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hnS := nS.isLt
  have hlt := lt_of_sub_ne nS _ hpe (h2 ▸ hR2)
  have hk : k = plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := hk2 hlt
  subst hk
  have hr1n : (S.regs 1).toNat = pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
    rw [h1]; exact add_toNat _ _ (by simp only [Nat.reducePow]; omega)
  have hbyte : S.mem.readLE (S.regs 1).toNat 1 = Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) := by
    rw [hr1n]; exact topSt_byte hSt hpC _ hlt
  have hacc1 : S.mem.accessible (S.regs 1).toNat 1 false = true := by
    rw [topSt_acc hSt, hr1n]; exact Arm64.Memory.accessible_mono _ hpA (by omega) (by omega)
  have hbl := Arm64.Memory.readLE_lt s.mem (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) 1
  have hbr : ¬ (BitVec.setWidth 32 (BitVec.ofNat 64 (S.mem.readLE (S.regs 1).toNat 1))).toNat = 48 := by
    rw [hbyte, byte_eqc _ _ (by simpa [Fv256.C.bytesAt] using hbl) (by omega)]; exact hbz
  have hbyte2 : S.mem.readLE (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) 1 = Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) := by
    rw [← hr1n]; exact hbyte
  have hacc2 : S.mem.accessible (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) 1 false = true := by
    rw [← hr1n]; exact hacc1
  have hbr2 : ¬ (BitVec.setWidth 32 (BitVec.ofNat 64 (S.mem.readLE (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) 1))).toNat = 48 := by
    rw [← hr1n]; exact hbr
  have hsp : startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat :=
    Fv256.TopMath.startPos_nz _ _ hlt hbz
  janus_run [hpc, hR2, hacc1, hbr, hacc2, hbr2] until [0xb8a18]
  all_goals (
    refine ⟨hSt, ?_, ⟨_, Nat.le_refl _, fun _ => rfl, ?_⟩, ?_⟩
    · simp [setReg_apply, h0]
    · rw [hsp]; simp [setReg_apply, h1]
    · simp [setReg_apply, h2, hsp, sub_ofNat nS _ hpe])

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- the first byte of the stripped number is `'0'`: spill and enter the zero-skip loop -/
theorem top_b2 (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 0xb89f4)
    (hA : PostA R R2 T b L lo hi z pS nS s S) (hR2 : S.regs 2 ≠ 0#64)
    (hbz : Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) = 48) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (BitVec.ofNat 64 0xb8ab0) S
      (LoopInv R R2 T b L lo hi z pS nS s 0) := by
  obtain ⟨hSt, h0, h2, k, hk1, hk2, h1⟩ := hA
  obtain ⟨hl1, hl2, h0', h1', h2', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hpe := Fv256.TopMath.plusEnd_le (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hnS := nS.isLt
  have hlt := lt_of_sub_ne nS _ hpe (h2 ▸ hR2)
  have hk : k = plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := hk2 hlt
  subst hk
  have hr1n : (S.regs 1).toNat = pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
    rw [h1]; exact add_toNat _ _ (by simp only [Nat.reducePow]; omega)
  have hbyte : S.mem.readLE (S.regs 1).toNat 1 = Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) := by
    rw [hr1n]; exact topSt_byte hSt hpC _ hlt
  have hacc1 : S.mem.accessible (S.regs 1).toNat 1 false = true := by
    rw [topSt_acc hSt, hr1n]; exact Arm64.Memory.accessible_mono _ hpA (by omega) (by omega)
  have hbl := Arm64.Memory.readLE_lt s.mem (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) 1
  have hbr : (BitVec.setWidth 32 (BitVec.ofNat 64 (S.mem.readLE (S.regs 1).toNat 1))).toNat = 48 := by
    rw [hbyte, byte_eqc _ _ (by simpa [Fv256.C.bytesAt] using hbl) (by omega)]; exact hbz
  have hbyte2 : S.mem.readLE (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) 1 = Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) := by
    rw [← hr1n]; exact hbyte
  have hacc2 : S.mem.accessible (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) 1 false = true := by
    rw [← hr1n]; exact hacc1
  have hbr2 : (BitVec.setWidth 32 (BitVec.ofNat 64 (S.mem.readLE (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) 1))).toNat = 48 := by
    rw [← hr1n]; exact hbr
  have hspS := topSt_sp hSt (by omega)
  have hwacc : S.mem.accessible (S.sp.toNat + 56) 16 true = true := by
    rw [topSt_acc hSt]; exact Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  janus_run [hpc, hR2, hacc1, hbr, hacc2, hbr2, hwacc] until [0xb8ab0]
  all_goals (
    have hv1 : (18446744073709551616 - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + nS.toNat) % 256 ^ 8 = nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
      rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; omega
    have hv2 : (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) % 256 ^ 8 = pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
      rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (by omega)
    have hmf : MemFrame S.mem ((S.mem.writeLE (BitVec.toNat S.sp + 56) 8
              (18446744073709551616 - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + nS.toNat)).writeLE
          (BitVec.toNat S.sp + 64) 8 (pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)) [(lo, hi)] := by
      repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
    refine ⟨?st, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlt, Nat.zero_le _, fun k hk => absurd hk (by omega)⟩
    case st =>
      refine topSt_step hMod.1 hSt (by omega) rfl (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) hmf (by omega) ?_ ?_ ?_ ?_ ?_ ?_ <;>
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    · simp [setReg_apply, h0]
    · simp [setReg_apply, h1]
    · simp [setReg_apply, h2, sub_ofNat nS _ hpe]
    · simp [setReg_apply]
    · simp [setReg_apply]
    · have : s.sp.toNat - 24 = S.sp.toNat + 56 := by omega
      rw [this]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      exact hv1
    · have : s.sp.toNat - 16 = S.sp.toNat + 64 := by omega
      rw [this]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      exact hv2)

end Fv256.Arm64.SfdTop
