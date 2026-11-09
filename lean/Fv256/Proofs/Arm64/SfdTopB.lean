import Fv256.Proofs.Arm64.SfdTopA
import Fv256.Proofs.Arm64.SfdDecode

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

/-- the exit of the zero skip at index `i` (pc `0xb8b08`) -/
def TailInv (i : Nat) (S : State) : Prop :=
  TopSt R R2 T b L lo hi z pS s S ∧ S.regs 0 = z ∧
    S.regs 1 = pS + BitVec.ofNat 64 (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
    S.regs 2 = BitVec.ofNat 64 (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
    S.regs 3 = BitVec.ofNat 64 i ∧ i < nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
    startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + i

/-- after a zero byte, before the two register moves (pc `0xb8aa8`) -/
def LoopMid (j : Nat) (S : State) : Prop :=
  TopSt R R2 T b L lo hi z pS s S ∧ S.regs 0 = z ∧
    S.regs 1 = pS + BitVec.ofNat 64 (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
    S.regs 2 = BitVec.ofNat 64 (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) ∧
    S.regs 3 = BitVec.ofNat 64 j ∧ S.regs 5 = BitVec.ofNat 64 (j + 1) ∧
    S.mem.readLE (s.sp.toNat - 24) 8 = nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
    S.mem.readLE (s.sp.toNat - 16) 8 = pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
    plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < nS.toNat ∧
    j + 1 ≤ nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
    (∀ k, k < j + 1 → Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + k) = 48)

/-- at the `decoderune` call (pc `0x7f6e0`): what the continuation needs -/
def DecCtx (j : Nat) (S : State) : Prop :=
  TopSt R R2 T b L lo hi z pS s S ∧ S.regs 30 = BitVec.ofNat 64 0xb8ae0 ∧
    S.mem.readLE (S.sp.toNat + 48) 8 = j ∧
    S.mem.readLE (S.sp.toNat + 56) 8 = nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
    S.mem.readLE (S.sp.toNat + 64) 8 = pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
    j < nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ∧
    startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j

end Defs

theorem topSt_acc {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {z pS : BitVec 64}
    {s S : State} (hS : TopSt R R2 T b L lo hi z pS s S) (a n : Nat) (w : Bool) :
    S.mem.accessible a n w = s.mem.accessible a n w := hS.2.2.2.2.1.accessible a n w

theorem topSt_byte {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {z pS nS : BitVec 64}
    {s S : State} (hS : TopSt R R2 T b L lo hi z pS s S) (hpC : nS.toNat = 0 ∨ pS.toNat + nS.toNat ≤ lo ∨ hi ≤ pS.toNat)
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
    rw [topSt_acc hSt, hr1n]; exact Arm64.Memory.accessible_mono _ (hpA.resolve_left (by omega)) (by omega) (by omega)
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
    rw [topSt_acc hSt, hr1n]; exact Arm64.Memory.accessible_mono _ (hpA.resolve_left (by omega)) (by omega) (by omega)
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

theorem mask_i (len k : BitVec 64) (hk : k.toNat < len.toNat) (hl : len.toNat < 2 ^ 63) :
    k &&& (k - len).sshiftRight 63 = k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  exact Fv256.Arm64.SfdDecode.mask_keep' len k hk hl

theorem r1_eq (pS : BitVec 64) (a b : Nat) : BitVec.ofNat 64 b + (pS + BitVec.ofNat 64 a) = pS + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofNat_add]; bv_omega

theorem r2_eq (m i : Nat) (h : i ≤ m) (hm : m < 2 ^ 64) : BitVec.ofNat 64 m - BitVec.ofNat 64 i = BitVec.ofNat 64 (m - i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at hm ⊢
  omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- `s = s[i:]` and back to the length compare -/
theorem top_tail (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S : State) (i : Nat) (hpc : S.pc = BitVec.ofNat 64 0xb8b08)
    (hT : TailInv R R2 T b L lo hi z pS nS s i S) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (BitVec.ofNat 64 0xb8a18) S
      (TopMid R R2 T b L lo hi z pS nS s) := by
  obtain ⟨hSt, h0, h1, h2, h3, hi1, hsp⟩ := hT
  obtain ⟨hl1, hl2, h0', h1', h2', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  have hnS := nS.isLt
  have hpe := Fv256.TopMath.plusEnd_le (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hm := mask_i (BitVec.ofNat 64 (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)) (BitVec.ofNat 64 i)
    (by simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega) (by simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega)
  have hlt : ¬ ((BitVec.ofNat 64 i).toNat > (BitVec.ofNat 64 (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)).toNat) := by
    simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  janus_run [hpc, h1, h2, h3, hm, hlt] until [0xb8a18]
  all_goals (
    have hmm : nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < 2 ^ 64 := by omega
    refine ⟨hSt, ?_, ⟨plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + i, ?_, ?_, ?_⟩, ?_⟩
    · simp [setReg_apply, h0]
    · rw [hsp]; omega
    · intro _; rw [hsp]
    · simp only [setReg_apply]; simp; rw [r1_eq]
    · simp only [setReg_apply]; simp; rw [r2_eq _ _ (by omega) hmm, hsp]; congr 1; omega)

theorem ofNat_toInt (n : Nat) (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).toInt = (n : Int) := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
  simp only [Nat.reducePow]
  split <;> omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- one more zero byte: back to the loop head -/
theorem top_ls (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S : State) (j : Nat) (hpc : S.pc = BitVec.ofNat 64 0xb8ab0)
    (hI : LoopInv R R2 T b L lo hi z pS nS s j S) (hjm : j + 1 ≤ nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)
    (hbz : Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) = 48) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (BitVec.ofNat 64 0xb8aa8) S
      (LoopMid R R2 T b L lo hi z pS nS s j) := by
  obtain ⟨hSt, h0, h1, h2, h3, h4, m56, m64, hlt, hjle, hzs⟩ := hI
  obtain ⟨hl1, hl2, h0', h1', h2', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  have hnS := nS.isLt
  have hpe := Fv256.TopMath.plusEnd_le (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hjI := ofNat_toInt j (by omega)
  have hmI := ofNat_toInt (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (by omega)
  have hacc3 : S.mem.accessible (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 false = true := by
    rw [topSt_acc hSt]; exact Arm64.Memory.accessible_mono _ (hpA.resolve_left (by omega)) (by omega) (by omega)
  have hbyte3 : S.mem.readLE (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 = 48 := by
    rw [topSt_byte hSt hpC _ (by omega)]; exact hbz
  have hf1 : (addSub (48#32) (127#32) true).snd = ⟨true, false, false, false⟩ := by decide
  have hf2 : (addSub (48#32) (48#32) true).snd = ⟨false, true, true, false⟩ := by decide
  janus_run [hpc, h1, h2, h3, hjI, hmI, hacc3, hbyte3, hf1, hf2] until [0xb8aa8]
  all_goals (
    refine ⟨hSt, ?_, ?_, ?_, ?_, ?_, m56, m64, hlt, hjm, ?_⟩
    · simp [setReg_apply, h0]
    · simp [setReg_apply, h1]
    · simp [setReg_apply, h2]
    · simp [setReg_apply, h3]
    · simp [setReg_apply, BitVec.ofNat_add]
    · intro k hk
      by_cases hkj : k < j
      · exact hzs k hkj
      · have : k = j := by omega
        subst this; exact hbz)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- the two register moves of the loop back edge -/
theorem top_hop (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State)
    (S : State) (j : Nat) (hpc : S.pc = BitVec.ofNat 64 0xb8aa8)
    (hI : LoopMid R R2 T b L lo hi z pS nS s j S) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (BitVec.ofNat 64 0xb8ab0) S
      (LoopInv R R2 T b L lo hi z pS nS s (j + 1)) := by
  obtain ⟨hSt, h0, h1, h2, h3, h5, m56, m64, hlt, hjle, hzs⟩ := hI
  janus_run [hpc] until [0xb8ab0]
  all_goals (
    refine ⟨hSt, ?_, ?_, ?_, ?_, ?_, m56, m64, hlt, hjle, hzs⟩
    · simp [setReg_apply, h0]
    · simp [setReg_apply, h1]
    · simp [setReg_apply, h2]
    · simp [setReg_apply, h5]
    · simp [setReg_apply, h3])

theorem flags127 : ∀ x : Fin 256, (addSub (BitVec.setWidth 32 (BitVec.ofNat 64 x.val)) 127#32 true).snd =
    ⟨decide (x.val < 127), decide (x.val = 127), decide (127 ≤ x.val), false⟩ := by decide +kernel

theorem flags48 : ∀ x : Fin 256, (addSub (BitVec.setWidth 32 (BitVec.ofNat 64 x.val)) 48#32 true).snd =
    ⟨decide (x.val < 48), decide (x.val = 48), decide (48 ≤ x.val), false⟩ := by decide +kernel

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- a non-zero ASCII byte ends the zero run -/
theorem top_lb (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S : State) (j : Nat) (hpc : S.pc = BitVec.ofNat 64 0xb8ab0)
    (hI : LoopInv R R2 T b L lo hi z pS nS s j S) (hjm : j + 1 ≤ nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)
    (hb127 : Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) ≤ 127)
    (hb48 : Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) ≠ 48) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (BitVec.ofNat 64 0xb8b08) S
      (TailInv R R2 T b L lo hi z pS nS s j) := by
  obtain ⟨hSt, h0, h1, h2, h3, h4, m56, m64, hlt, hjle, hzs⟩ := hI
  obtain ⟨hl1, hl2, h0', h1', h2', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  have hnS := nS.isLt
  have hpe := Fv256.TopMath.plusEnd_le (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hjI := ofNat_toInt j (by omega)
  have hmI := ofNat_toInt (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (by omega)
  have hacc3 : S.mem.accessible (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 false = true := by
    rw [topSt_acc hSt]; exact Arm64.Memory.accessible_mono _ (hpA.resolve_left (by omega)) (by omega) (by omega)
  have hbyte3 : S.mem.readLE (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 =
      Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) := by
    rw [topSt_byte hSt hpC _ (by omega)]; rfl
  have hbl := Arm64.Memory.readLE_lt S.mem (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1
  have hbl' : S.mem.readLE (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 < 256 := by simpa using hbl
  have hf1 := flags127 ⟨_, hbl'⟩
  have hf2 := flags48 ⟨_, hbl'⟩
  have hx48 : ¬ S.mem.readLE (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 = 48 := by
    rw [hbyte3]; exact hb48
  have hx127 : S.mem.readLE (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 ≤ 127 := by
    rw [hbyte3]; exact hb127
  rcases Nat.lt_or_eq_of_le hx127 with hx | hx
  · janus_run [hpc, h1, h2, h3, hjI, hmI, hacc3, hf1, hf2, hx, hx48] until [0xb8b08]

    all_goals (
      refine ⟨hSt, ?_, ?_, ?_, ?_, by omega, Fv256.TopMath.startPos_a _ _ _ (by omega) hb48 hzs⟩
      · simp [setReg_apply, h0]
      · simp [setReg_apply, h1]
      · simp [setReg_apply, h2]
      · simp [setReg_apply, h3])
  · janus_run [hpc, h1, h2, h3, hjI, hmI, hacc3, hf1, hf2, hx, hx48] until [0xb8b08]
    all_goals (
      refine ⟨hSt, ?_, ?_, ?_, ?_, by omega, Fv256.TopMath.startPos_a _ _ _ (by omega) hb48 hzs⟩
      · simp [setReg_apply, h0]
      · simp [setReg_apply, h1]
      · simp [setReg_apply, h2]
      · simp [setReg_apply, h3])

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- the whole stripped number is zeros: keep the last `'0'` -/
theorem top_lend (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S : State) (j : Nat) (hpc : S.pc = BitVec.ofNat 64 0xb8ab0)
    (hI : LoopInv R R2 T b L lo hi z pS nS s j S) (hjm : nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat ≤ j) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (BitVec.ofNat 64 0xb8b08) S
      (TailInv R R2 T b L lo hi z pS nS s (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat - 1)) := by
  obtain ⟨hSt, h0, h1, h2, h3, h4, m56, m64, hlt, hjle, hzs⟩ := hI
  obtain ⟨hl1, hl2, h0', h1', h2', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  have hnS := nS.isLt
  have hpe := Fv256.TopMath.plusEnd_le (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hjeq : j = nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by omega
  have hjI := ofNat_toInt j (by omega)
  have hmI := ofNat_toInt (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (by omega)
  have hsp : startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = nS.toNat - 1 :=
    Fv256.TopMath.startPos_b _ _ hlt (fun k hk1 hk2 => by
      have := hzs (k - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (by omega)
      rwa [show plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + (k - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) = k by omega] at this)
  janus_run [hpc, h1, h2, h3, h4, hjI, hmI] until [0xb8b08]
  all_goals (
    refine ⟨hSt, ?_, ?_, ?_, ?_, by omega, by omega⟩
    · simp [setReg_apply, h0]
    · simp [setReg_apply, h1]
    · simp [setReg_apply, h2]
    · simp [setReg_apply, h4]; congr 1; omega)

theorem flags_ge128 (x : Nat) (hx : 128 ≤ x) (hx2 : x < 256) : (addSub (BitVec.setWidth 32 (BitVec.ofNat 64 x)) 127#32 true).snd =
    ⟨false, false, true, false⟩ := by
  have := flags127 ⟨x, hx2⟩
  simp only at this
  rw [this]
  have h1 : ¬ x < 127 := by omega
  have h2 : ¬ x = 127 := by omega
  simp [h1, h2]; omega

theorem ld1_post (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S S' : State) (j : Nat) (hSt : TopSt R R2 T b L lo hi z pS s S)
    (hlt : plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < nS.toNat)
    (hjm : j + 1 ≤ nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)
    (hsp : startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)
    (h1 : S'.sp = S.sp) (h29 : S'.regs 29 = S.regs 29) (h28 : S'.regs 28 = S.regs 28) (h18 : S'.regs 18 = S.regs 18)
    (r0 : S'.regs 0 = pS + BitVec.ofNat 64 (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat))
    (r1 : S'.regs 1 = BitVec.ofNat 64 (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat))
    (r2 : S'.regs 2 = BitVec.ofNat 64 j) (r30 : S'.regs 30 = BitVec.ofNat 64 0xb8ae0)
    (m56 : S.mem.readLE (S.sp.toNat + 56) 8 = nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)
    (m64 : S.mem.readLE (S.sp.toNat + 64) 8 = pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)
    (hmem : S'.mem = S.mem.writeLE (S.sp.toNat + 48) 8 j) :
    Fv256.Arm64.SfdDecode.DecPre (pS + BitVec.ofNat 64 (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat))
          (BitVec.ofNat 64 (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)) (BitVec.ofNat 64 j) S' ∧
        DecCtx R R2 T b L lo hi z pS nS s j S' := by
  obtain ⟨hl1, hl2, h0', h1', h2', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hnS := nS.isLt
  have hpe := Fv256.TopMath.plusEnd_le (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hspS := topSt_sp hSt (by omega)
  have hmf : MemFrame S.mem S'.mem [(lo, hi)] := by
    rw [hmem]
    refine MemFrame.writeLE (MemFrame.refl _ _) _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  have hSt' : TopSt R R2 T b L lo hi z pS s S' := by
    refine topSt_step hMod.1 hSt (by omega) h1 h29 h28 h18 hmf (by omega) ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (rw [hmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint])
  have hEnvS := hSt'.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18⟩ := hEnvS
  have hspS' : S'.sp.toNat = s.sp.toNat - 80 := by rw [h1]; exact hspS
  have hlim : pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < 2 ^ 64 := by omega
  have hP := add_toNat pS _ hlim
  have hmN : (BitVec.ofNat 64 (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)).toNat = nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
    simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  have hjN : (BitVec.ofNat 64 j).toNat = j := by simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  refine ⟨⟨by rw [r30]; decide, by rw [r30]; decide, ⟨f6, f7, by omega⟩, ⟨f4, by omega, by omega, ?_⟩, r0, r1, r2, ?_, ?_, ?_, ?_⟩,
    hSt', r30, ?_, ?_, ?_, by omega, hsp⟩
  · exact Arm64.Memory.accessible_mono _ f5 (by omega) (by omega)
  · rw [hP, hmN, topSt_acc hSt']; exact Arm64.Memory.accessible_mono _ (hpA.resolve_left (by omega)) (by omega) (by omega)
  · rw [hP, hmN]; omega
  · rw [hjN, hmN]; omega
  · rw [hP, h1]; omega
  · rw [hmem, h1]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
    rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (by omega)
  · rw [hmem, h1]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact m56
  · rw [hmem, h1]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact m64

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- a byte `>= 0x80`: up to the `runtime.decoderune` call -/
theorem top_ld1 (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S : State) (j : Nat) (hpc : S.pc = BitVec.ofNat 64 0xb8ab0)
    (hI : LoopInv R R2 T b L lo hi z pS nS s j S) (hjm : j + 1 ≤ nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)
    (hb128 : 128 ≤ Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (BitVec.ofNat 64 Fv256.Arm64.SfdDecode.dr) S
      (fun S' => Fv256.Arm64.SfdDecode.DecPre (pS + BitVec.ofNat 64 (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat))
          (BitVec.ofNat 64 (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat)) (BitVec.ofNat 64 j) S' ∧
        DecCtx R R2 T b L lo hi z pS nS s j S') := by
  have hpre' := hpre
  obtain ⟨hSt, h0, h1, h2, h3, h4, m56, m64, hlt, hjle, hzs⟩ := hI
  obtain ⟨hl1, hl2, h0', h1', h2', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hnS := nS.isLt
  have hpe := Fv256.TopMath.plusEnd_le (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hjI := ofNat_toInt j (by omega)
  have hmI := ofNat_toInt (nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) (by omega)
  have hspS := topSt_sp hSt (by omega)
  have hacc3 : S.mem.accessible (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 false = true := by
    rw [topSt_acc hSt]; exact Arm64.Memory.accessible_mono _ (hpA.resolve_left (by omega)) (by omega) (by omega)
  have hbyte3 : S.mem.readLE (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 =
      Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) := by
    rw [topSt_byte hSt hpC _ (by omega)]; rfl
  have hbl := Arm64.Memory.readLE_lt S.mem (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1
  have hbl' : S.mem.readLE (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 < 256 := by simpa using hbl
  have hx128 : 128 ≤ S.mem.readLE (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 := by
    rw [hbyte3]; exact hb128
  have hf1 := flags127 ⟨_, hbl'⟩
  have hxa : ¬ S.mem.readLE (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 < 127 := by omega
  have hxb : ¬ S.mem.readLE (pS.toNat + (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) 1 = 127 := by omega
  have hwacc : S.mem.accessible (S.sp.toNat + 48) 24 true = true := by
    rw [topSt_acc hSt]; exact Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  have m56' : S.mem.readLE (S.sp.toNat + 56) 8 = nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
    rw [show S.sp.toNat + 56 = s.sp.toNat - 24 by omega]; exact m56
  have m64' : S.mem.readLE (S.sp.toNat + 64) 8 = pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
    rw [show S.sp.toNat + 64 = s.sp.toNat - 16 by omega]; exact m64
  janus_run [hpc, h1, h2, h3, hjI, hmI, hacc3, hf1, hxa, hxb, hwacc] until [0x7f6e0]
  all_goals (
    refine ReachesRet.done (by first | rfl | decide) ?_
    exact ld1_post R R2 T b L lo hi z pS nS s hpre' S _ j hSt hlt hjm (Fv256.TopMath.startPos_a _ _ _ (by omega) (by omega) hzs) rfl rfl rfl rfl (by simp [setReg_apply])
      (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) m56' m64' rfl)

theorem cmp_z (E c : BitVec 32) : (addSub E c true).snd.z = decide (E - c = 0#32) := by
  show decide ((addWithCarry E (~~~c) true).1 = 0#32) = _
  rw [addWithCarry_not_true_fst]

theorem rune_ne48 (r : BitVec 64) (h1 : 128 ≤ r.toNat) (h2 : r.toNat < 2 ^ 32) :
    (addSub (BitVec.setWidth 32 r) 48#32 true).snd.z = false := by
  rw [cmp_z]
  simp only [decide_eq_false_iff_not]
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
  simp only [Nat.reducePow] at this h2
  omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- after `runtime.decoderune`: the rune is not `'0'`, so the zero run ends at `j` -/
theorem top_ld2 (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s)
    (S' S'' : State) (j : Nat) (hpc : S''.pc = BitVec.ofNat 64 0xb8ae0)
    (hC : DecCtx R R2 T b L lo hi z pS nS s j S') (hpost : Fv256.Arm64.SfdDecode.DecPost S' S'') :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (BitVec.ofNat 64 0xb8b08) S''
      (TailInv R R2 T b L lo hi z pS nS s j) := by
  obtain ⟨hSt, hr30, c48, c56, c64, hjlt, hsp⟩ := hC
  obtain ⟨p1, p29, p28, p18, p0lo, p0hi, pf⟩ := hpost
  obtain ⟨hl1, hl2, h0', h1', h2', hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hMaxA, hMaxO, hMaxR, hMaxB, hErrA, hErrO, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA⟩ := hpre
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hnS := nS.isLt
  have hpe := Fv256.TopMath.plusEnd_le (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
  have hspS := topSt_sp hSt (by omega)
  have hmf : MemFrame S'.mem S''.mem [(lo, hi)] := by
    refine MemFrame.mono pf (fun a n ha => ?_)
    simp only [outside_cons, outside_nil, and_true] at ha ⊢
    omega
  have hSt'' : TopSt R R2 T b L lo hi z pS s S'' := by
    refine topSt_step hMod.1 hSt (by omega) p1 p29 p28 p18 hmf (by omega) ?_ ?_ ?_ ?_ ?_ ?_ <;>
      exact pf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hz48 := rune_ne48 (S''.regs 0) p0lo (by simpa using p0hi)
  have hz0 : S''.mem.readLE (S''.sp.toNat + 88) 8 = z.toNat := by
    have := hSt''.2.2.2.2.2.2.2.1
    rw [show S''.sp.toNat + 88 = s.sp.toNat + 8 by rw [p1]; omega]; exact this
  have hjN : (BitVec.ofNat 64 j).toNat = j := by simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
  have hr48 : S''.mem.readLE (S''.sp.toNat + 48) 8 = j := by
    rw [p1, pf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact c48
  have hr56 : S''.mem.readLE (S''.sp.toNat + 56) 8 = nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
    rw [p1, pf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact c56
  have hr64 : S''.mem.readLE (S''.sp.toNat + 64) 8 = pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by
    rw [p1, pf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact c64
  have hspS2 : S''.sp.toNat = s.sp.toNat - 80 := by rw [p1]; exact hspS
  have hacc : S''.mem.accessible (S''.sp.toNat + 48) 48 false = true := by
    rw [pf.accessible, topSt_acc hSt]
    exact Arm64.Memory.accessible_mono _ (Arm64.Memory.accessible_weaken _ e5) (by omega) (by omega)
  have hlim : pS.toNat + plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < 2 ^ 64 := by omega
  have hz0' : S'.mem.readLE (S'.sp.toNat + 88) 8 = z.toNat := by
    have := hSt.2.2.2.2.2.2.2.1
    rw [show S'.sp.toNat + 88 = s.sp.toNat + 8 by omega]; exact this
  have hpS : BitVec.ofNat 64 pS.toNat = pS := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hzz : BitVec.ofNat 64 z.toNat = z := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  janus_run [hpc, hr48, hr56, hr64, hz0, hz48, hacc] until [0xb8b08]
  all_goals (
    refine ⟨topSt_step hMod.1 hSt'' (by omega) p1.symm (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) (MemFrame.refl _ _) (by omega) rfl rfl rfl rfl rfl rfl, ?_, ?_, ?_, ?_, hjlt, hsp⟩
    · simp [setReg_apply, hz0', hzz]
    · simp [setReg_apply, c64, BitVec.ofNat_add, hpS]
    · simp [setReg_apply, c56]
    · simp [setReg_apply, c48])

open Fv256.Arm64.SegCompose in
set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- the zero-skip loop, by induction on the bytes left -/
theorem top_loop (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpre : TopPre cfg R R2 T b L lo hi z pS nS s) :
    ∀ (k j : Nat) (S : State), nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat - j = k →
      S.pc = BitVec.ofNat 64 0xb8ab0 → LoopInv R R2 T b L lo hi z pS nS s j S →
      ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (BitVec.ofNat 64 0xb8a18) S
        (TopMid R R2 T b L lo hi z pS nS s) := by
  intro k
  induction k with
  | zero =>
    intro j S hk hpc hI
    have hjle := hI.2.2.2.2.2.2.2.2.2.1
    refine seg_trans (top_lend impl R R2 T b L lo hi z pS nS s hpre S j hpc hI (by omega)) ?_
    intro S1 hpc1 hT
    exact top_tail impl R R2 T b L lo hi z pS nS s hpre S1 _ hpc1 hT
  | succ k ih =>
    intro j S hk hpc hI
    have hI' := hI
    obtain ⟨hSt, h0, h1, h2, h3, h4, m56, m64, hlt, hjle, hzs⟩ := hI'
    have hjm : j + 1 ≤ nS.toNat - plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat := by omega
    by_cases hx48 : Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) = 48
    · refine seg_trans (top_ls impl R R2 T b L lo hi z pS nS s hpre S j hpc hI hjm hx48) ?_
      intro S1 hpc1 hM
      refine seg_trans (top_hop impl R R2 T b L lo hi z pS nS s S1 j hpc1 hM) ?_
      intro S2 hpc2 hI2
      exact ih (j + 1) S2 (by omega) hpc2 hI2
    · by_cases hx127 : Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) ≤ 127
      · refine seg_trans (top_lb impl R R2 T b L lo hi z pS nS s hpre S j hpc hI hjm hx127 hx48) ?_
        intro S1 hpc1 hT
        exact top_tail impl R R2 T b L lo hi z pS nS s hpre S1 _ hpc1 hT
      · have hb128 : 128 ≤ Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j) := by omega
        refine seg_trans (top_ld1 impl R R2 T b L lo hi z pS nS s hpre S j hpc hI hjm hb128) ?_
        intro S1 hpc1 hq
        obtain ⟨hdp, hC⟩ := hq
        refine ReachesRet.call (Fv256.Arm64.SfdDecode.decoderune_sum impl _ _ _) hpc1 hdp ?_
        intro S' hpc' hpost
        have hr30 := hC.2.1
        refine seg_trans (top_ld2 impl R R2 T b L lo hi z pS nS s hpre S1 S' j (by rw [hpc', hr30]) hC hpost) ?_
        intro S3 hpc3 hT
        exact top_tail impl R R2 T b L lo hi z pS nS s hpre S3 _ hpc3 hT

open Fv256.Arm64.SegCompose in
set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- from the entry to the length compare: the number starts at `startPos` -/
theorem top_to_mid (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 0xb89b0)
    (hpre : TopPre cfg R R2 T b L lo hi z pS nS s) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (BitVec.ofNat 64 0xb8a18) s
      (TopMid R R2 T b L lo hi z pS nS s) := by
  refine seg_trans (top_pro impl R R2 T b L lo hi z pS nS s hpc hpre) ?_
  intro S hpc1 hA
  by_cases hR2 : S.regs 2 = 0#64
  · exact top_b0 impl R R2 T b L lo hi z pS nS s S hpc1 hA hR2
  · by_cases hbz : Fv256.C.bytesAt s.mem pS.toNat (plusEnd (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat) = 48
    · refine seg_trans (top_b2 impl R R2 T b L lo hi z pS nS s hpre S hpc1 hA hR2 hbz) ?_
      intro S1 hpc2 hI
      have hlt := hI.2.2.2.2.2.2.2.2.1
      exact top_loop impl R R2 T b L lo hi z pS nS s hpre _ 0 S1 rfl hpc2 hI
    · exact top_b1 impl R R2 T b L lo hi z pS nS s hpre S hpc1 hA hR2 hbz

end Fv256.Arm64.SfdTop
