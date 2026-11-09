import Extracted
import Fv256.Proofs.Amd64.ScanSpec
import Fv256.Proofs.Amd64.ScanCfg
import Fv256.Proofs.Amd64.ScanIbsCall
import Fv256.Proofs.Amd64.ScanSfd
import Fv256.Proofs.Amd64.ScanSfd2
import Fv256.Proofs.Amd64.ScanIdx
import Fv256.Proofs.Amd64.ScanA6
import Fv256.Proofs.Common.MulOverflowProg
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Amd64.MoLib.Top
open Fv256.Amd64.ScanSfd
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanCfg

namespace Fv256.Amd64.ScanA

/-- the library summary of `Exp` at the entry of `Exp` in the consumer program `P`, over the rodata of the Scan extraction; the extra
conjunct `fsBase` is the frame fact the library summary does not state (see HANDOVER 4) -/
def ExpSumm (P : Janus.Amd64.Program) : Prop :=
  Summary P expEntry
    (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
      0x100 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0x20 ∧ StackWritable s 0xa8 0x20 ∧ s.xmm 15 = 0 ∧
      Buffer s (s.regs 0) 32 true ∧ Buffer s (s.regs 3) 32 false ∧ Buffer s (s.regs 1) 32 false ∧
      ((s.regs 0).toNat + 32 ≤ (s.regs 4).toNat - 0xa8 ∨ (s.regs 4).toNat + 0x20 ≤ (s.regs 0).toNat) ∧
      ((s.regs 3).toNat + 32 ≤ (s.regs 4).toNat - 0xa8 ∨ (s.regs 4).toNat + 0x20 ≤ (s.regs 3).toNat) ∧
      ((s.regs 1).toNat + 32 ≤ (s.regs 4).toNat - 0xa8 ∨ (s.regs 4).toNat + 0x20 ≤ (s.regs 1).toNat) ∧
      ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 0xa8 ∨ (s.regs 4).toNat + 0x20 ≤ (s.regs 14).toNat + 16) ∧
      Extracted.program.DataLoaded s.mem)
    (fun s s' => s'.regs 0 = s.regs 0 ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
      s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
      s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.expSpec (s.mem.readLE (s.regs 3).toNat 32) (s.mem.readLE (s.regs 1).toNat 32) ∧
      MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat - 0xa8, (s.regs 4).toNat + 0x20)] ∧
      s'.fsBase = s.fsBase)

/-- the library summary of `MulOverflow` (plus the frame facts `fsBase`, `df`) at its entry in the consumer program `P` -/
def MoSumm (P : Janus.Amd64.Program) (z x y : BitVec 64) : Prop :=
  Summary P Fv256.MulOverflowProg.entry
    (fun s => ∃ ret, RetAddr Fv256.MulOverflowProg.program ret ∧
      CallSetup (Fv256.MulOverflowProg.program.withExit ret) Fv256.MulOverflowProg.entry [z, x, y] s ∧
      (StackGuardOK s 0 ∧ StackWritable s 152 16 ∧ (s.regs regSP).toNat % 8 = 0 ∧
      Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Fv256.Amd64.MoLib.Alias z x ∧ Fv256.Amd64.MoLib.Alias z y ∧
      Fv256.Amd64.MoLib.Alias x y ∧
      (z.toNat + 32 ≤ (s.regs regSP).toNat - 152 ∨ (s.regs regSP).toNat + 16 ≤ z.toNat) ∧
      (x.toNat + 32 ≤ (s.regs regSP).toNat - 152 ∨ (s.regs regSP).toNat + 16 ≤ x.toNat) ∧
      (y.toNat + 32 ≤ (s.regs regSP).toNat - 152 ∨ (s.regs regSP).toNat + 16 ≤ y.toNat)))
    (fun s s' => (ABIReturn s s' ∧ (s'.regs 0 = z ∧
      (s'.regs 3).toNat % 256 = (if Fv256.Spec.W ≤ valueAt s x 32 * valueAt s y 32 then 1 else 0) ∧
      valueAt s' z 32 = Fv256.Spec.mul (valueAt s x 32) (valueAt s y 32) ∧
      Fv256.Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 152) 168)) ∧ s'.fsBase = s.fsBase ∧ s'.df = s.df)

theorem base10 (m : Janus.Arm64.Memory) (a : Nat) :
    (((m.writeLE a 16 0).writeLE (a + 16) 16 0).writeLE a 8 10).readLE a 32 = 10 := by
  rw [Util.readLE_32]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
  simp

set_option maxRecDepth 100000 in
/-- segment 6a: exponent above 77: `ErrBig256Range` -/
theorem sci_range1 (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (i v e : Nat) (s S5 : State) (hpc : S5.rip = BitVec.ofNat 64 (sci + 0x129))
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat ≠ 0)
    (hI : Inv5 Extracted.program R R2 T b L lo hi dst p n i v e s S5) (hbig : 77 < e) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S5 (SciPost cfg R R2 b L lo hi dst p n s) := by
  obtain ⟨hret0, hT, hlo, hav, hpg, htls, hout, hinit⟩ := hpre
  obtain ⟨q4, q5, q14, qx, qdf, qfs, qMF, qEnv, qi, qdst, qp, qn, qret, qrbp, qsome, qlt, qdec, qnn, qdece, qval, qvale, qdl⟩ := hI
  have hsp := (s.regs 4).isLt
  have hlo4 : lo + 4800 ≤ (s.regs 4).toNat := hT.lo4
  have hhi : (s.regs 4).toNat + 32 ≤ hi := hT.hi32
  have hEnv : Env cfg R R2 T b L lo hi s := hT.env
  have e1 : lo ≤ (s.regs 4).toNat := hEnv.1
  have hhi48 : hi ≤ 2 ^ 48 := hEnv.2.2.1
  have hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 := hret0.2.1
  have hwin5 : S5.mem.accessible lo (hi - lo) true = true := by rw [qMF.accessible]; exact hEnv.2.2.2.2.1
  have hx15 : s.xmm 15 = 0 := hret0.2.2.1
  have herr : S5.mem.accessible cfg.errBig 16 false = true := by rw [qMF.accessible]; exact hT.errAcc
  have herr0 : S5.mem.readLE cfg.errBig 8 = s.mem.readLE cfg.errBig 8 := by
    rw [qMF.readLE _ _ (by have := hT.errOut; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega)]
  have herr1 : S5.mem.readLE (cfg.errBig + 8) 8 = s.mem.readLE (cfg.errBig + 8) 8 := by
    rw [qMF.readLE _ _ (by have := hT.errOut; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega)]
  have hex := Util.readLE_32 S5.mem ((s.regs 4).toNat - 40)
  have hl0 := Util.readLE8_lt S5.mem ((s.regs 4).toNat - 40)
  clear hT hEnv hret0 qEnv qdl
  by_cases hA : 77 < S5.mem.readLE ((s.regs 4).toNat - 40) 8
  · janus64_run [qi, qn, qp, qret, qrbp, q4, hwin5, hra, herr, herr0, herr1, hA]
    have hsc : sciParse (bytesAt s.mem p.toNat) n.toNat = .range := by
      rw [sci_tail_ok _ _ _ _ hn qsome qdec qnn e qdece]
      simp [hbig]
    unfold SciPost
    refine ⟨?_, Or.inr (Or.inr (Or.inl ⟨hsc, ?_, ?_⟩)), ?_⟩
    · simp [Kept, retAddrOf, setRegF_apply]
      exact ⟨q14, by rw [qx, hx15], qfs⟩
    · show (BitVec.ofNat 64 (S5.mem.readLE cfg.errBig 8)).toNat = _
      rw [herr0, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Util.readLE8_lt _ _)
    · show (BitVec.ofNat 64 (S5.mem.readLE (cfg.errBig + 8) 8)).toNat = _
      rw [herr1, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Util.readLE8_lt _ _)
    · exact qMF.mono (fun a k h => by simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; exact h.2)
  · have hex' : S5.mem.readLE ((s.regs 4).toNat - 40) 32 = S5.mem.readLE ((s.regs 4).toNat - 40) 8 + 2 ^ 64 * S5.mem.readLE ((s.regs 4).toNat - 32) 8 +
        2 ^ 128 * S5.mem.readLE ((s.regs 4).toNat - 24) 8 + 2 ^ 192 * S5.mem.readLE ((s.regs 4).toNat - 16) 8 := by
      have := Util.readLE_32 S5.mem ((s.regs 4).toNat - 40)
      rwa [show (s.regs 4).toNat - 40 + 8 = (s.regs 4).toNat - 32 by omega, show (s.regs 4).toNat - 40 + 16 = (s.regs 4).toNat - 24 by omega,
        show (s.regs 4).toNat - 40 + 24 = (s.regs 4).toNat - 16 by omega] at this
    have hl1 := Util.readLE8_lt S5.mem ((s.regs 4).toNat - 32)
    have hl2 := Util.readLE8_lt S5.mem ((s.regs 4).toNat - 24)
    have hl3 := Util.readLE8_lt S5.mem ((s.regs 4).toNat - 16)
    have hup : ¬ ((BitVec.ofNat 64 (S5.mem.readLE ((s.regs 4).toNat - 32) 8) ||| BitVec.ofNat 64 (S5.mem.readLE ((s.regs 4).toNat - 24) 8) |||
        BitVec.ofNat 64 (S5.mem.readLE ((s.regs 4).toNat - 16) 8)).toNat = 0) := by
      intro h
      rw [BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hl1, Nat.mod_eq_of_lt hl2, Nat.mod_eq_of_lt hl3] at h
      obtain ⟨h12, h3⟩ := Nat.or_eq_zero_iff.mp h
      obtain ⟨h1, h2⟩ := Nat.or_eq_zero_iff.mp h12
      have hv : S5.mem.readLE ((s.regs 4).toNat - 40) 32 = e := qvale
      rw [h1, h2, h3] at hex'
      omega
    janus64_run [qi, qn, qp, qret, qrbp, q4, hwin5, hra, herr, herr0, herr1, hA, hup]
    have hsc : sciParse (bytesAt s.mem p.toNat) n.toNat = .range := by
      rw [sci_tail_ok _ _ _ _ hn qsome qdec qnn e qdece]
      simp [hbig]
    unfold SciPost
    refine ⟨?_, Or.inr (Or.inr (Or.inl ⟨hsc, ?_, ?_⟩)), ?_⟩
    · simp [Kept, retAddrOf, setRegF_apply]
      exact ⟨q14, by rw [qx, hx15], qfs⟩
    · show (BitVec.ofNat 64 (S5.mem.readLE cfg.errBig 8)).toNat = _
      rw [herr0, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Util.readLE8_lt _ _)
    · show (BitVec.ofNat 64 (S5.mem.readLE (cfg.errBig + 8) 8)).toNat = _
      rw [herr1, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Util.readLE8_lt _ _)
    · exact qMF.mono (fun a k h => by simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; exact h.2)



theorem _root_.Fv256.Amd64.SfdTopSpec.TopPre0.zg (h : TopPre0 C R R2 T b L lo hi z p n s) :
    (s.regs 14).toNat + 16 + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 14).toNat + 16 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem bv_sub_toNat (x : BitVec 64) (k : Nat) (hk : k < 2 ^ 64) (h : k ≤ x.toNat) : (x - BitVec.ofNat 64 k).toNat = x.toNat - k := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]; omega

theorem mf_of_ow2 {m m' : Janus.Arm64.Memory} {p n q k : Nat} (h : Fv256.Util.OnlyWrites2 m m' p n q k) :
    MemFrame m m' [(p, p + n), (q, q + k)] :=
  ⟨fun a j hout => by
    simp only [outside_cons, outside_nil, and_true] at hout
    exact Janus.Arm64.Memory.readLE_congr fun i hi => h.2 _ (by omega) (by omega),
   fun a j w => Janus.Arm64.Memory.accessible_congr h.1 a j w⟩

/-- the state `S6` after `Exp(&exp, &base, &exp)` returned (at `sci + 0x17e`): the local `exp` holds `10^e` -/
def Inv6 (P : Janus.Amd64.Program) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (dst p n : BitVec 64) (v e : Nat) (s S6 : State) : Prop :=
  S6.regs 4 = s.regs 4 - 112#64 ∧ S6.regs 5 = s.regs 4 - 8#64 ∧ S6.regs 14 = s.regs 14 ∧ S6.xmm 15 = 0 ∧ S6.df = s.df ∧
  S6.fsBase = s.fsBase ∧ MemFrame s.mem S6.mem [(lo, hi), (dst.toNat, dst.toNat + 32)] ∧
  S6.mem.readLE ((s.regs 4).toNat + 8) 8 = dst.toNat ∧ S6.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 ∧
  S6.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧
  sciParse (bytesAt s.mem p.toNat) n.toNat = (if 2 ^ 256 ≤ v * 10 ^ e then Res.range else Res.ok (v * 10 ^ e)) ∧
  Janus.Spec.val256 S6.mem dst.toNat = v ∧ Janus.Spec.val256 S6.mem ((s.regs 4).toNat - 40) = 10 ^ e ∧ P.DataLoaded S6.mem

/-- the state `S7` after `MulOverflow(dst, dst, &exp)` returned (at `sci + 0x190`) -/
def Inv7 (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (dst p n : BitVec 64) (v e : Nat) (s S7 : State) : Prop :=
  S7.regs 4 = s.regs 4 - 112#64 ∧ S7.regs 5 = s.regs 4 - 8#64 ∧ S7.regs 14 = s.regs 14 ∧ S7.xmm 15 = 0 ∧ S7.df = s.df ∧
  S7.fsBase = s.fsBase ∧ MemFrame s.mem S7.mem [(lo, hi), (dst.toNat, dst.toNat + 32)] ∧
  S7.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 ∧
  S7.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧
  sciParse (bytesAt s.mem p.toNat) n.toNat = (if 2 ^ 256 ≤ v * 10 ^ e then Res.range else Res.ok (v * 10 ^ e)) ∧
  (S7.regs 3).toNat % 256 = (if 2 ^ 256 ≤ v * 10 ^ e then 1 else 0) ∧
  Janus.Spec.val256 S7.mem dst.toNat = (v * 10 ^ e) % 2 ^ 256

set_option maxRecDepth 100000 in
/-- segment 7b: the overflow test and the returns -/
theorem sci_aftmo (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (v e : Nat) (s S7 : State) (hpc : S7.rip = BitVec.ofNat 64 (sci + 0x190))
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat ≠ 0)
    (hI : Inv7 R R2 T b L lo hi dst p n v e s S7) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S7 (SciPost cfg R R2 b L lo hi dst p n s) := by
  obtain ⟨hret0, hT, hlo, hav, hpg, htls, hout, hinit⟩ := hpre
  obtain ⟨q4, q5, q14, qx, qdf, qfs, qMF, qret, qrbp, qsc, qfl, qval⟩ := hI
  have hsp := (s.regs 4).isLt
  have hlo4 : lo + 4800 ≤ (s.regs 4).toNat := hT.lo4
  have hhi : (s.regs 4).toNat + 32 ≤ hi := hT.hi32
  have hEnv : Env cfg R R2 T b L lo hi s := hT.env
  have e1 : lo ≤ (s.regs 4).toNat := hEnv.1
  have hhi48 : hi ≤ 2 ^ 48 := hEnv.2.2.1
  have hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 := hret0.2.1
  have hx15 : s.xmm 15 = 0 := hret0.2.2.1
  have hwin7 : S7.mem.accessible lo (hi - lo) true = true := by rw [qMF.accessible]; exact hEnv.2.2.2.2.1
  have hacc7 : S7.mem.accessible ((s.regs 4).toNat - 8) 16 false = true := by
    rw [qMF.accessible]
    exact Janus.Arm64.Memory.accessible_sub s.mem hEnv.2.2.2.2.1 (Or.inl rfl) (by omega) (by omega)
  have herr : S7.mem.accessible cfg.errBig 16 false = true := by rw [qMF.accessible]; exact hT.errAcc
  have herr0 : S7.mem.readLE cfg.errBig 8 = s.mem.readLE cfg.errBig 8 := by
    rw [qMF.readLE _ _ (by have := hT.errOut; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega)]
  have herr1 : S7.mem.readLE (cfg.errBig + 8) 8 = s.mem.readLE (cfg.errBig + 8) 8 := by
    rw [qMF.readLE _ _ (by have := hT.errOut; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega)]
  clear hT hEnv hret0
  have hlow : ((S7.regs 3).toNat % 256 = 0 ↔ BitVec.setWidth 8 (S7.regs 3) = 0#8) := by
    constructor
    · intro h; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]; omega
    · intro h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_setWidth] at this; omega
  by_cases hov : 2 ^ 256 ≤ v * 10 ^ e
  · have hbl : ¬ BitVec.setWidth 8 (S7.regs 3) = 0#8 := fun h => by
      have := hlow.2 h; simp only [hov, ↓reduceIte] at qfl; omega
    janus64_run [qret, qrbp, q4, hra, hacc7, herr, herr0, herr1, hbl]
    unfold SciPost
    refine ⟨?_, Or.inr (Or.inr (Or.inl ⟨by rw [qsc]; simp only [hov, ↓reduceIte], ?_, ?_⟩)), ?_⟩
    · simp [Kept, retAddrOf, setRegF_apply]
      exact ⟨q14, by rw [qx, hx15], qfs⟩
    · show (BitVec.ofNat 64 (S7.mem.readLE cfg.errBig 8)).toNat = _
      rw [herr0, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Util.readLE8_lt _ _)
    · show (BitVec.ofNat 64 (S7.mem.readLE (cfg.errBig + 8) 8)).toNat = _
      rw [herr1, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Util.readLE8_lt _ _)
    · exact qMF.mono (fun a k h => by simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; exact h.2)
  · have hbl : BitVec.setWidth 8 (S7.regs 3) = 0#8 := by
      apply hlow.1; simp only [hov, ↓reduceIte] at qfl; omega
    janus64_run [qret, qrbp, q4, hra, hacc7, hbl]
    have hlt : v * 10 ^ e < 2 ^ 256 := Nat.lt_of_not_le hov
    unfold SciPost
    refine ⟨?_, Or.inl ⟨v * 10 ^ e, by rw [qsc]; simp only [hov, ↓reduceIte], by simp [setRegF_apply], by simp [setRegF_apply], ?_⟩, ?_⟩
    · simp [Kept, retAddrOf, setRegF_apply]
      exact ⟨q14, by rw [qx, hx15], qfs⟩
    · rw [qval]; exact Nat.mod_eq_of_lt hlt
    · exact qMF.mono (fun a k h => by simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; exact h.2)

set_option maxRecDepth 100000 in
/-- segment 7a: the `MulOverflow` call, its pre- and postcondition -/
theorem sci_mocall (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (v e : Nat) (s S6 S3 : State)
    (hmo : ∀ z x y, MoSumm (Extracted.program.link impl) z x y) (he : e ≤ 77)
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat ≠ 0)
    (hI : Inv6 Extracted.program R R2 T b L lo hi dst p n v e s S6)
    (hpc : S3.rip = BitVec.ofNat 64 moEntry) (hr0 : S3.regs 0 = dst) (hr3 : S3.regs 3 = dst)
    (hr1 : S3.regs 1 = s.regs 4 - 40#64) (hr4 : S3.regs 4 = s.regs 4 - 120#64) (hr5 : S3.regs 5 = s.regs 4 - 8#64)
    (hr14 : S3.regs 14 = s.regs 14) (hxm : S3.xmm 15 = 0) (hdf : S3.df = s.df) (hfs : S3.fsBase = s.fsBase)
    (hmem : S3.mem = S6.mem.writeLE ((s.regs 4).toNat - 120) 8 4930928) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S3 (SciPost cfg R R2 b L lo hi dst p n s) := by
  have hpre0 := hpre
  obtain ⟨hret0, hT, hlo, hav, hpg, htls, hout, hinit⟩ := hpre
  obtain ⟨q4, q5, q14, qx, qdf, qfs, qMF, qdst, qret, qrbp, qsc, qvd, qve, qdl⟩ := hI
  have hsp := (s.regs 4).isLt
  have hlo4 : lo + 4800 ≤ (s.regs 4).toNat := hT.lo4
  have hhi : (s.regs 4).toNat + 32 ≤ hi := hT.hi32
  have hEnv : Env cfg R R2 T b L lo hi s := hT.env
  have e1 : lo ≤ (s.regs 4).toNat := hEnv.1
  have hhi48 : hi ≤ 2 ^ 48 := hEnv.2.2.1
  have hwin : s.mem.accessible lo (hi - lo) true = true := hEnv.2.2.2.2.1
  have hr14b : (s.regs 14).toNat + 24 ≤ 2 ^ 48 := hEnv.2.2.2.2.2.1
  have hg1 : s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := hEnv.2.2.2.2.2.2.1
  have hg2 : s.mem.readLE ((s.regs 14).toNat + 16) 8 < lo := hEnv.2.2.2.2.2.2.2.1
  have hzg := hT.zg
  have hdzw := hT.zwin
  have hdacc : s.mem.accessible dst.toNat 32 true = true := hT.zacc
  have hdb : dst.toNat + 32 ≤ 2 ^ 48 := hT.zbuf
  have hx15 : s.xmm 15 = 0 := hret0.2.2.1
  have hdf0 : s.df = false := hret0.2.2.2
  have hs40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := bv_sub_toNat _ 40 (by omega) (by omega)
  have hs120 : (S3.regs 4).toNat = (s.regs 4).toNat - 120 := by rw [hr4]; exact bv_sub_toNat _ 120 (by omega) (by omega)
  have hwin6 : S6.mem.accessible lo (hi - lo) true = true := by rw [qMF.accessible]; exact hwin
  have hF1 : MemFrame S6.mem S3.mem [(lo, hi)] := by
    rw [hmem]
    exact (MemFrame.refl S6.mem _).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  have hF0 : MemFrame s.mem S3.mem [(lo, hi), (dst.toNat, dst.toNat + 32)] :=
    qMF.trans (hF1.mono (fun a k h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; exact h.1))
      (rs'' := [(lo, hi), (dst.toNat, dst.toNat + 32)]) (fun a k h => ⟨h, h⟩)
  have hacc3 : S3.mem.accessible lo (hi - lo) true = true := by rw [hF1.accessible]; exact hwin6
  have hret3 : S3.mem.readLE ((s.regs 4).toNat - 120) 8 = 4930928 := by
    rw [hmem, Janus.Arm64.Memory.readLE_writeLE_self]
  have hvd : valueAt S3 dst 32 = v := by
    show S3.mem.readLE dst.toNat 32 = v
    rw [hF1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact qvd
  have hvy : valueAt S3 (s.regs 4 - 40#64) 32 = 10 ^ e := by
    show S3.mem.readLE (s.regs 4 - 40#64).toNat 32 = 10 ^ e
    rw [hs40, hmem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    exact qve
  have hpow : 10 ^ e < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) he) (by decide)
  have hmoA := hmo dst dst (s.regs 4 - 40#64)
  refine ReachesRet.call_regions hmoA (by rw [hpc]; rfl) ?_ (fun S' hr hq hregs => ?_)
  · refine ⟨4930928, RetAddr.of_check (by decide), ⟨?_, ?_, hxm, by simp only [List.length_cons, List.length_nil]; decide, ?_, hdf.trans hdf0⟩, ?_⟩
    · rw [hpc]; rfl
    · show S3.mem.readLE (S3.regs 4).toNat 8 = 4930928
      rw [hs120]; exact hret3
    · intro i hi'
      simp only [List.length_cons, List.length_nil] at hi'
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · exact hr0
      · exact hr3
      · exact hr1
    · have hsp3 : (S3.regs regSP).toNat = (s.regs 4).toNat - 120 := hs120
      have hg3 : (s.regs 14).toNat + 16 + 8 ≤ lo ∨ hi ≤ (s.regs 14).toNat + 16 := hEnv.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hg2' : S3.mem.readLE ((s.regs 14).toNat + 16) 8 < lo := by
        rw [hF0.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hg2
      have hg : StackGuardOK S3 0 :=
        ⟨by simp only [regG, stackguard0Offset, hr14]; omega, by simp only [regG, stackguard0Offset, hr14]; rw [hF0.accessible]; exact hg1,
         by simp only [stackguard0, stackguard0Offset, regG, hr14]; omega⟩
      have e4 : (s.regs 4).toNat % 8 = 0 := hEnv.2.2.2.1
      have hexpacc : S3.mem.accessible (s.regs 4 - 40#64).toNat 32 false = true := by
        rw [hs40]; exact Janus.Arm64.Memory.accessible_sub S3.mem hacc3 (Or.inl rfl) (by omega) (by omega)
      have hdacc3 : S3.mem.accessible dst.toNat 32 true = true := by rw [hF0.accessible]; exact hdacc
      refine ⟨hg, ⟨by omega, by omega, ?_⟩, by omega, ⟨hdb, hdacc3⟩, ⟨hdb, ?_⟩, ⟨by omega, hexpacc⟩, Or.inl rfl, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [regSP, hs120]
        exact Janus.Arm64.Memory.accessible_sub S3.mem hacc3 (Or.inr rfl) (by omega) (by omega)
      · rw [Janus.Arm64.Memory.accessible_read_of_write _ hdacc3]
      · rcases hdzw with h | h
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))
      · rcases hdzw with h | h
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))
      · rcases hdzw with h | h
        · left; omega
        · right; omega
      · rcases hdzw with h | h
        · left; omega
        · right; omega
      · right; omega
  · obtain ⟨⟨⟨abis, abif, abig, abiz⟩, k0, kfl, kval, kow⟩, kfs, kdf⟩ := hq
    have hr' : S'.rip = BitVec.ofNat 64 (sci + 0x190) := by
      rw [hr]; unfold retAddrOf; rw [hs120, hret3]; rfl
    have hsp3 : (S3.regs regSP).toNat = (s.regs 4).toNat - 120 := hs120
    have hS7 : S'.regs 4 = s.regs 4 - 112#64 := by
      have : S'.regs regSP = S3.regs 4 + 8#64 := abis
      rw [this, hr4]; bv_omega
    have hMFo : MemFrame S3.mem S'.mem [(dst.toNat, dst.toNat + 32), ((S3.regs regSP).toNat - 152, (S3.regs regSP).toNat - 152 + 168)] :=
      mf_of_ow2 kow
    rw [hsp3] at hMFo
    have hMF5 : MemFrame s.mem S'.mem [(lo, hi), (dst.toNat, dst.toNat + 32)] :=
      hF0.trans hMFo (rs'' := [(lo, hi), (dst.toNat, dst.toNat + 32)]) (fun a k h => ⟨h, by
        simp only [outside_cons, outside_nil, and_true] at h ⊢; omega⟩)
    have hslot : ∀ a k, ((s.regs 4).toNat - 8 ≤ a) → a + k ≤ hi →
        S'.mem.readLE a k = S6.mem.readLE a k := by
      intro a k h1 h2
      rw [hMFo.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega), hmem]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have hWdef : Fv256.Spec.W = 2 ^ 256 := rfl
    refine sci_aftmo impl R R2 T b L lo hi dst p n v e s S' hr' hpre0 hn ?_
    refine ⟨hS7, ?_, ?_, ?_, ?_, ?_, hMF5, ?_, ?_, qsc, ?_, ?_⟩
    · have : S'.regs regFP = S3.regs 5 := abif
      rw [this, hr5]
    · have : S'.regs regG = S3.regs 14 := abig
      rw [this, hr14]
    · have : S'.xmm xmmZero = S3.xmm 15 := abiz
      rw [this, hxm]
    · rw [kdf, hdf]
    · rw [kfs, hfs]
    · rw [hslot _ _ (by omega) (by omega)]; exact qret
    · rw [hslot _ _ (by omega) (by omega)]; exact qrbp
    · rw [kfl, hvd, hvy, hWdef]
    · have : valueAt S' dst 32 = Fv256.Spec.mul (valueAt S3 dst 32) (valueAt S3 (s.regs 4 - 40#64) 32) := kval
      show valueAt S' dst 32 = _
      rw [this, hvd, hvy]; rfl

set_option maxRecDepth 100000 in
/-- segment 7: the `MulOverflow` call and the overflow test -/
theorem sci_aftexp (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (v e : Nat) (s S6 : State) (hpc : S6.rip = BitVec.ofNat 64 (sci + 0x17e))
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat ≠ 0)
    (hmo : ∀ z x y, MoSumm (Extracted.program.link impl) z x y) (he : e ≤ 77)
    (hI : Inv6 Extracted.program R R2 T b L lo hi dst p n v e s S6) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S6 (SciPost cfg R R2 b L lo hi dst p n s) := by
  have hpre0 := hpre
  have hI0 := hI
  obtain ⟨hret0, hT, hlo, hav, hpg, htls, hout, hinit⟩ := hpre
  obtain ⟨q4, q5, q14, qx, qdf, qfs, qMF, qdst, qret, qrbp, qsc, qvd, qve, qdl⟩ := hI
  have hsp := (s.regs 4).isLt
  have hlo4 : lo + 4800 ≤ (s.regs 4).toNat := hT.lo4
  have hhi : (s.regs 4).toNat + 32 ≤ hi := hT.hi32
  have hEnv : Env cfg R R2 T b L lo hi s := hT.env
  have e1 : lo ≤ (s.regs 4).toNat := hEnv.1
  have hhi48 : hi ≤ 2 ^ 48 := hEnv.2.2.1
  have hwin6 : S6.mem.accessible lo (hi - lo) true = true := by rw [qMF.accessible]; exact hEnv.2.2.2.2.1
  have hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 := hret0.2.1
  have hdst : (BitVec.ofNat 64 (S6.mem.readLE ((s.regs 4).toNat + 8) 8)) = dst := by rw [qdst, BitVec.ofNat_toNat]; simp
  clear hT hEnv hret0 qdl
  janus64_run [hwin6, qdst, qret, q4, hra] until [moEntry]
  exact sci_mocall impl R R2 T b L lo hi dst p n v e s S6 _ hmo he hpre0 hn hI0 rfl rfl rfl rfl rfl q5 q14 qx rfl qfs rfl

set_option maxRecDepth 100000 in
/-- segment 6c: the `Exp` call and its result -/
theorem sci_expcall (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (i v e : Nat) (s S5 S3 : State)
    (hexp : ExpSumm (Extracted.program.link impl)) (hmo : ∀ z x y, MoSumm (Extracted.program.link impl) z x y)
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat ≠ 0)
    (hI : Inv5 Extracted.program R R2 T b L lo hi dst p n i v e s S5) (hbig : ¬ 77 < e)
    (hpc : S3.rip = BitVec.ofNat 64 expEntry) (hr0 : S3.regs 0 = s.regs 4 - 40#64) (hr3 : S3.regs 3 = s.regs 4 - 72#64)
    (hr1 : S3.regs 1 = s.regs 4 - 40#64) (hr4 : S3.regs 4 = s.regs 4 - 120#64) (hr5 : S3.regs 5 = s.regs 4 - 8#64)
    (hr14 : S3.regs 14 = s.regs 14) (hxm : S3.xmm 15 = 0) (hdf : S3.df = s.df) (hfs : S3.fsBase = s.fsBase)
    (hmem : S3.mem = (((S5.mem.writeLE ((s.regs 4).toNat - 72) 16 0).writeLE ((s.regs 4).toNat - 56) 16 0).writeLE
      ((s.regs 4).toNat - 72) 8 10).writeLE ((s.regs 4).toNat - 120) 8 4930910) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S3 (SciPost cfg R R2 b L lo hi dst p n s) := by
  have hpre0 := hpre
  obtain ⟨hret0, hT, hlo, hav, hpg, htls, hout, hinit⟩ := hpre
  obtain ⟨q4, q5, q14, qx, qdf, qfs, qMF, qEnv, qi, qdst, qp, qn, qret, qrbp, qsome, qlt, qdec, qnn, qdece, qval, qvale, qdl⟩ := hI
  have hsp := (s.regs 4).isLt
  have hlo4 : lo + 4800 ≤ (s.regs 4).toNat := hT.lo4
  have hhi : (s.regs 4).toNat + 32 ≤ hi := hT.hi32
  have hEnv : Env cfg R R2 T b L lo hi s := hT.env
  have e1 : lo ≤ (s.regs 4).toNat := hEnv.1
  have hhi48 : hi ≤ 2 ^ 48 := hEnv.2.2.1
  have hwin : s.mem.accessible lo (hi - lo) true = true := hEnv.2.2.2.2.1
  have hwin5 : S5.mem.accessible lo (hi - lo) true = true := by rw [qMF.accessible]; exact hwin
  have hdf0 : s.df = false := hret0.2.2.2
  have hr14b : (s.regs 14).toNat + 24 ≤ 2 ^ 48 := hEnv.2.2.2.2.2.1
  have hg1 : s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := hEnv.2.2.2.2.2.2.1
  have hg2 : s.mem.readLE ((s.regs 14).toNat + 16) 8 < lo := hEnv.2.2.2.2.2.2.2.1
  have hg3 : (s.regs 14).toNat + 16 + 8 ≤ lo ∨ hi ≤ (s.regs 14).toNat + 16 := hEnv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzg := hT.zg
  have hs40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := bv_sub_toNat _ 40 (by omega) (by omega)
  have hs72 : (s.regs 4 - 72#64).toNat = (s.regs 4).toNat - 72 := bv_sub_toNat _ 72 (by omega) (by omega)
  have hs120 : (S3.regs 4).toNat = (s.regs 4).toNat - 120 := by rw [hr4]; exact bv_sub_toNat _ 120 (by omega) (by omega)
  have hs120' : (s.regs 4 - 120#64).toNat = (s.regs 4).toNat - 120 := bv_sub_toNat _ 120 (by omega) (by omega)
  have hF1 : MemFrame S5.mem S3.mem [(lo, hi)] := by
    rw [hmem]
    exact (((MemFrame.refl S5.mem _).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)
      |>.writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  have hF0 : MemFrame s.mem S3.mem [(lo, hi), (dst.toNat, dst.toNat + 32)] :=
    qMF.trans (hF1.mono (fun a k h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; exact h.1))
      (rs'' := [(lo, hi), (dst.toNat, dst.toNat + 32)]) (fun a k h => ⟨h, h⟩)
  have hacc3 : S3.mem.accessible lo (hi - lo) true = true := by rw [hF1.accessible]; exact hwin5
  have hdl3 : Extracted.program.DataLoaded S3.mem := by
    refine dl_frame qdl ?_ hF1 ?_ ?_
    · rw [hmem]; simp only [Janus.Arm64.Memory.regions_writeLE]
    · intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rw [hr]; simp <;> omega
    · intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rw [hr]; exact hwin5
  have hret3 : S3.mem.readLE ((s.regs 4).toNat - 120) 8 = 4930910 := by
    rw [hmem, Janus.Arm64.Memory.readLE_writeLE_self]
  have hg2' : S3.mem.readLE ((s.regs 14).toNat + 16) 8 < lo := by
    rw [hF0.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hg2
  have hbase : S3.mem.readLE ((s.regs 4).toNat - 72) 32 = 10 := by
    have := base10 S5.mem ((s.regs 4).toNat - 72)
    rw [show (s.regs 4).toNat - 72 + 16 = (s.regs 4).toNat - 56 by omega] at this
    rw [hmem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    exact this
  refine ReachesRet.call_regions hexp hpc ?_ (fun S' hr hq hregs => ?_)
  · simp only [hr0, hr3, hr1, hr4, hs40, hs72, hs120', hr14]
    have hsp3 : (S3.regs regSP).toNat = (s.regs 4).toNat - 120 := hs120
    have hg : StackGuardOK S3 0x20 :=
      ⟨by simp only [regG, stackguard0Offset, hr14]; omega, by simp only [regG, stackguard0Offset, hr14]; rw [hF0.accessible]; exact hg1,
       by simp only [stackguard0, stackguard0Offset, regG, hr14]; omega⟩
    refine ⟨⟨?_, ?_⟩, by omega, hg, ⟨by omega, by omega, ?_⟩, hxm, ⟨by omega, ?_⟩, ⟨by omega, ?_⟩, ⟨by omega, ?_⟩, by omega, by omega, by omega, ?_, hdl3⟩
    · exact Janus.Arm64.Memory.accessible_sub S3.mem hacc3 (Or.inl rfl) (by omega) (by omega)
    · rw [hret3]; omega
    · simp only [regSP, hs120]
      exact Janus.Arm64.Memory.accessible_sub S3.mem hacc3 (Or.inr rfl) (by omega) (by omega)
    · exact Janus.Arm64.Memory.accessible_sub S3.mem hacc3 (Or.inr rfl) (by omega) (by omega)
    · exact Janus.Arm64.Memory.accessible_sub S3.mem hacc3 (Or.inl rfl) (by omega) (by omega)
    · exact Janus.Arm64.Memory.accessible_sub S3.mem hacc3 (Or.inl rfl) (by omega) (by omega)
    · omega
  · obtain ⟨k0, k4, k5, k14, kx, kdf, kmx, kval, kMF, kfs⟩ := hq
    have hr' : S'.rip = BitVec.ofNat 64 (sci + 0x17e) := by
      rw [hr]; unfold retAddrOf; rw [hs120, hret3]; rfl
    have he77 : e ≤ 77 := by omega
    have hpow : 10 ^ e < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) he77) (by decide)
    have hexpv : S3.mem.readLE ((s.regs 4).toNat - 40) 32 = e := by
      rw [hmem]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      exact qvale
    simp only [hr0, hs40, hs120, hr3, hs72, hr1] at kMF kval
    rw [hbase, hexpv] at kval
    have hexp10 : S'.mem.readLE ((s.regs 4).toNat - 40) 32 = 10 ^ e := by
      rw [kval]; unfold Fv256.F.expSpec; exact Nat.mod_eq_of_lt hpow
    have hMF5 : MemFrame s.mem S'.mem [(lo, hi), (dst.toNat, dst.toNat + 32)] :=
      hF0.trans kMF (rs'' := [(lo, hi), (dst.toNat, dst.toNat + 32)]) (fun a k h => ⟨h, by
        simp only [outside_cons, outside_nil, and_true] at h ⊢; omega⟩)
    have hdzw := hT.zwin
    have hslot : ∀ a k, ((s.regs 4).toNat - 8 ≤ a) → a + k ≤ hi →
        S'.mem.readLE a k = S5.mem.readLE a k := by
      intro a k h1 h2
      rw [kMF.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega), hmem]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have hdo : Outside dst.toNat 32 [(lo, hi)] := by
      have := hT.zwin
      simp only [outside_cons, outside_nil, and_true]; omega
    have hdlS : Extracted.program.DataLoaded S'.mem := by
      refine dl_frame hdl3 ?_ kMF ?_ ?_
      · exact hregs
      · intro r hr
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl <;> simp <;> omega
      · intro r hr
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl
        · simp only [Nat.add_sub_cancel_left]
          exact Janus.Arm64.Memory.accessible_sub S3.mem hacc3 (Or.inr rfl) (by omega) (by omega)
        · simp only [Nat.add_sub_cancel_left]
          exact Janus.Arm64.Memory.accessible_sub S3.mem hacc3 (Or.inr rfl) (by omega) (by omega)
    have hsc : sciParse (bytesAt s.mem p.toNat) n.toNat = if 2 ^ 256 ≤ v * 10 ^ e then Res.range else Res.ok (v * 10 ^ e) := by
      rw [sci_tail_ok _ _ _ _ hn qsome qdec qnn e qdece]
      simp [hbig]
    refine sci_aftexp impl R R2 T b L lo hi dst p n v e s S' hr' hpre0 hn hmo he77 ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hMF5, ?_, ?_, ?_, hsc, ?_, ?_, hdlS⟩
    · rw [k4, hr4]; bv_omega
    · rw [k5, hr5]
    · rw [k14, hr14]
    · rw [kx, hxm]
    · rw [kdf, hdf]
    · rw [kfs, hfs]
    · rw [hslot _ _ (by omega) (by omega)]; exact qdst
    · rw [hslot _ _ (by omega) (by omega)]; exact qret
    · rw [hslot _ _ (by omega) (by omega)]; exact qrbp
    · show S'.mem.readLE dst.toNat 32 = v
      rw [kMF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), hmem]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      exact qval
    · exact hexp10

set_option maxRecDepth 100000 in
/-- segment 6b (exponent at most 77): zero the base `Int`, store 10, set up the `Exp` call -/
theorem sci_exp1 (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (i v e : Nat) (s S5 : State) (hpc : S5.rip = BitVec.ofNat 64 (sci + 0x129))
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat ≠ 0)
    (hexp : ExpSumm (Extracted.program.link impl)) (hmo : ∀ z x y, MoSumm (Extracted.program.link impl) z x y)
    (hI : Inv5 Extracted.program R R2 T b L lo hi dst p n i v e s S5) (hbig : ¬ 77 < e) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S5 (SciPost cfg R R2 b L lo hi dst p n s) := by
  have hpre0 := hpre
  have hI0 := hI
  obtain ⟨hret0, hT, hlo, hav, hpg, htls, hout, hinit⟩ := hpre
  obtain ⟨q4, q5, q14, qx, qdf, qfs, qMF, qEnv, qi, qdst, qp, qn, qret, qrbp, qsome, qlt, qdec, qnn, qdece, qval, qvale, qdl⟩ := hI
  have hsp := (s.regs 4).isLt
  have hlo4 : lo + 4800 ≤ (s.regs 4).toNat := hT.lo4
  have hhi : (s.regs 4).toNat + 32 ≤ hi := hT.hi32
  have hEnv : Env cfg R R2 T b L lo hi s := hT.env
  have e1 : lo ≤ (s.regs 4).toNat := hEnv.1
  have hhi48 : hi ≤ 2 ^ 48 := hEnv.2.2.1
  have hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 := hret0.2.1
  have hwin5 : S5.mem.accessible lo (hi - lo) true = true := by rw [qMF.accessible]; exact hEnv.2.2.2.2.1
  have hex' : S5.mem.readLE ((s.regs 4).toNat - 40) 32 = S5.mem.readLE ((s.regs 4).toNat - 40) 8 + 2 ^ 64 * S5.mem.readLE ((s.regs 4).toNat - 32) 8 +
        2 ^ 128 * S5.mem.readLE ((s.regs 4).toNat - 24) 8 + 2 ^ 192 * S5.mem.readLE ((s.regs 4).toNat - 16) 8 := by
    have := Util.readLE_32 S5.mem ((s.regs 4).toNat - 40)
    rwa [show (s.regs 4).toNat - 40 + 8 = (s.regs 4).toNat - 32 by omega, show (s.regs 4).toNat - 40 + 16 = (s.regs 4).toNat - 24 by omega,
      show (s.regs 4).toNat - 40 + 24 = (s.regs 4).toNat - 16 by omega] at this
  have hl1 := Util.readLE8_lt S5.mem ((s.regs 4).toNat - 32)
  have hl2 := Util.readLE8_lt S5.mem ((s.regs 4).toNat - 24)
  have hl3 := Util.readLE8_lt S5.mem ((s.regs 4).toNat - 16)
  have hl0 := Util.readLE8_lt S5.mem ((s.regs 4).toNat - 40)
  have hv : S5.mem.readLE ((s.regs 4).toNat - 40) 32 = e := qvale
  have hA : ¬ 77 < S5.mem.readLE ((s.regs 4).toNat - 40) 8 := by omega
  have hup : (BitVec.ofNat 64 (S5.mem.readLE ((s.regs 4).toNat - 32) 8) ||| BitVec.ofNat 64 (S5.mem.readLE ((s.regs 4).toNat - 24) 8) |||
        BitVec.ofNat 64 (S5.mem.readLE ((s.regs 4).toNat - 16) 8)).toNat = 0 := by
    rw [BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hl1, Nat.mod_eq_of_lt hl2, Nat.mod_eq_of_lt hl3]
    have h1 : S5.mem.readLE ((s.regs 4).toNat - 32) 8 = 0 := by omega
    have h2 : S5.mem.readLE ((s.regs 4).toNat - 24) 8 = 0 := by omega
    have h3 : S5.mem.readLE ((s.regs 4).toNat - 16) 8 = 0 := by omega
    rw [h1, h2, h3]; rfl
  clear hT hEnv hret0 qEnv qdl
  janus64_run [qi, qn, qp, qret, qrbp, q4, hwin5, hra, hA, hup] until [expEntry]
  exact sci_expcall impl R R2 T b L lo hi dst p n i v e s S5 _ hexp hmo hpre0 hn hI0 hbig rfl rfl rfl rfl rfl q5 q14 qx rfl qfs rfl

set_option maxRecDepth 100000 in
/-- segments 6-7: the range test on the exponent, `Exp`, `MulOverflow` -/
theorem sci_after2 (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (i v e : Nat) (s S5 : State) (hpc : S5.rip = BitVec.ofNat 64 (sci + 0x129))
    (hexp : ExpSumm (Extracted.program.link impl)) (hmo : ∀ z x y, MoSumm (Extracted.program.link impl) z x y)
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat ≠ 0)
    (hI : Inv5 Extracted.program R R2 T b L lo hi dst p n i v e s S5) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S5 (SciPost cfg R R2 b L lo hi dst p n s) := by
  by_cases hbig : 77 < e
  · exact sci_range1 impl R R2 T b L lo hi dst p n i v e s S5 hpc hpre hn hI hbig
  · exact sci_exp1 impl R R2 T b L lo hi dst p n i v e s S5 hpc hpre hn hexp hmo hI hbig

end Fv256.Amd64.ScanA
