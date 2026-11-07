import Fv256.Arm64.UnmarshalDec
import Fv256.Arm64.FromHexLib

/-!
# `UnmarshalText` hex branch (arm64): from the state after `string(input)` (buffer `sp - 72`) to `FromHexPre` of the `fromHex` call (Extracted-free)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.UnmarshalSpec Fv256.Arm64.UnmarshalDec Fv256.Arm64.FromHexLib

namespace Fv256.Arm64.UnmarshalHex

variable (C : SfdCfg)

/-- the environment of the hex parser: the digit table and the package error variables (package-level data of the binary:
the table is read-only, the error variables are initialised interface values), outside the runtime-owned ranges and the
stack window and the receiver. -/
def HexEnv (R : RtInv) (lo hi : Nat) (z : BitVec 64) (s : State) : Prop :=
  (∀ c, c < 256 → s.mem.readLE (1002789 + c) 1 = (hexNib c).getD 255) ∧
  s.mem.accessible 1002789 256 false = true ∧
  Outside 1002789 256 [(lo, hi), (z.toNat, z.toNat + 32)] ∧ Outside 1002789 256 R.rt ∧
  s.mem.accessible 1792784 96 false = true ∧
  Outside 1792784 96 [(lo, hi), (z.toNat, z.toNat + 32)] ∧ Outside 1792784 96 R.rt ∧
  (∀ e, e < 6 → s.mem.readLE (errAddrOf e) 8 ≠ 0)

theorem hex_call_pre {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s S3 : State} {M0 m : Janus.Arm64.Memory} {r0 r1 : BitVec 64} {v29 ra : Nat}
    (hpre : PreU C sb st R R2 T b L lo hi z pI nI s) (henv : HexEnv R lo hi z s) (hn2 : 2 ≤ nI.toNat)
    (hP : SbPost R st b L s pI nI r0 r1 M0 m (s.sp.toNat - 72))
    (hM0c : M0 = (((s.mem.writeLE (s.sp.toNat - 112) 8 ra).writeLE (s.sp.toNat - 120) 8 v29).writeLE (s.sp.toNat + 16) 8 pI.toNat).writeLE
      (s.sp.toNat + 8) 8 z.toNat)
    (hr0 : S3.regs 0 = BitVec.ofNat 64 (m.readLE (s.sp.toNat + 8) 8)) (hr1 : S3.regs 1 = r0) (hr2 : S3.regs 2 = r1)
    (hsp3 : S3.sp = s.sp - 112#64) (hr28 : S3.regs 28 = s.regs 28)
    (h30a : (S3.regs 30).toNat % 4 = 0) (h30b : (S3.regs 30).toNat < 2 ^ 48)
    (hS3 : S3.mem = m) :
    FromHexPre z r0 nI S3 ∧
    (∀ k, k < nI.toNat → S3.mem.readLE (r0.toNat + k) 1 = s.mem.readLE (pI.toNat + k) 1) ∧
    MemFrame s.mem S3.mem (R.rt ++ [(lo, hi)]) := by
  obtain ⟨hMF, hSOA, hLF, hFr, hInv⟩ := hP
  have hp := hpre.toS
  have hlo4 := hp.lo4
  have hhi4 := hp.hi4
  have hbne : s.sp.toNat - 72 ≠ 0 := by omega
  rw [if_neg hbne] at hMF hLF
  obtain ⟨hSO, hSA⟩ := hSOA
  have hEnv := hp.env
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv
  have hn : r1.toNat = nI.toNat := by
    rw [hSO.1]; simp
  have hr2' : S3.regs 2 = nI := by rw [hr2]; exact BitVec.eq_of_toNat_eq hn
  have hM0 := m0_frame C hpre hM0c
  have hzr : BitVec.ofNat 64 (m.readLE (s.sp.toNat + 8) 8) = z := by
    have ho : Outside (s.sp.toNat + 8) 8 (R.rt ++ [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8),
        (s.sp.toNat - 112 + 8, s.sp.toNat - 112 + 8 + 24)] ++ [(s.sp.toNat - 72, s.sp.toNat - 72 + 32)]) := by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      refine ⟨⟨Outside.of_sub e9 (by omega) (by omega), ?_, ?_⟩, ?_⟩ <;> omega
    rw [hMF.readLE _ _ ho, hM0c]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_mod]
    have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    rw [h8]; exact Nat.mod_eq_of_lt z.isLt
  rw [hzr] at hr0
  have hadds : ((if 2 ≤ r1.toNat ∧ (s.sp.toNat - 72 = 0 ∨ 32 < r1.toNat) then
          (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) ++
        (if 2 ≤ r1.toNat ∧ (s.sp.toNat - 72 = 0 ∨ 32 < r1.toNat) then []
         else if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)])) =
      (if nI.toNat = 0 then [] else [(r0.toNat, r0.toNat + nI.toNat)]) := by
    rw [Fv256.Arm64.SbtsFacts.adds_eq, hn]
  rw [hadds] at hInv
  rw [hn] at hSO hSA
  have hwin2 : MemFrame M0 m (R.rt ++ [(lo, hi)]) := by
    refine MemFrame.mono hMF ?_
    intro a n h
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨⟨h1, ?_, ?_⟩, ?_⟩ <;> omega
  have hF1 : MemFrame s.mem m (R.rt ++ [(lo, hi)]) := by
    refine hM0.trans hwin2 ?_
    intro a n h
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨h.2, h⟩
  have hF : MemFrame s.mem S3.mem (R.rt ++ [(lo, hi)]) := by
    rw [hS3]; exact hF1
  have hpos : 0 < nI.toNat := by omega
  have hz0 : nI.toNat ≠ 0 := by omega
  have hfr : 32 < nI.toNat → ApartAll r0.toNat nI.toNat L := by
    intro h32
    have := hFr
    rw [hn] at this
    rw [if_pos (by omega), if_neg hz0] at this
    simpa using this _ (List.mem_singleton_self _)
  obtain ⟨hlw, hlp, hlz⟩ := Fv256.Arm64.SbtsFacts.loc (hi3 := s.sp.toNat - 72) hSA hpos (by omega) (by omega)
    (Nat.le_refl _) (by omega) e9 e10 hp.init.2.2.2.2 (Mod.priv C hp.mod) hp.stWin hp.stPriv hp.stZ hp.zwin hp.zR hbne hfr
  have hlw2 : r0.toNat + nI.toNat ≤ lo ∨ s.sp.toNat - 72 ≤ r0.toNat := by
    have h := hlw
    simp only [outside_cons, outside_nil, and_true] at h
    exact h
  have hbytes : ∀ k, k < nI.toNat → S3.mem.readLE (r0.toNat + k) 1 = s.mem.readLE (pI.toNat + k) 1 := by
    intro k hk
    have hq := congrArg (fun l => l.getD k 0) hSO.2.2.2
    rw [strBytes_getD _ _ _ _ (by omega), strBytes_getD _ _ _ _ (by omega)] at hq
    rw [hS3, Janus.Arm64.Memory.readLE_one, Janus.Arm64.Memory.readLE_one]
    exact hq
  refine ⟨?_, hbytes, hF⟩
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := henv
  have hsp : S3.sp.toNat = s.sp.toNat - 112 := by
    rw [hsp3]; have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have t3' := t3
  have t6' := t6
  simp only [outside_cons, outside_nil, and_true] at t3' t6'
  have hzbuf := hp.zbuf
  have hzw := hp.zwin
  have hio : ∀ a n, Outside a n R.rt → Outside a n [(lo, hi)] → S3.mem.readLE a n = s.mem.readLE a n :=
    fun a n h1 h2 => hF.readLE a n (by rw [outside_append]; exact ⟨h1, h2⟩)
  have hS3acc : ∀ a n w, S3.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hF.accessible a n w
  have hlz' := hlz
  have e6' := e6
  unfold FromHexPre
  refine ⟨h30a, by omega, hr0, hr1, hr2', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by rw [hS3acc]; exact hzbuf.1, hzbuf.2⟩
  · exact ⟨by rw [hS3acc]; exact hSO.2.2.1 hpos, hSO.2.1⟩
  · intro c hc
    rw [hio _ _ (Outside.of_sub t4 (by omega) (by omega)) (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact t1 c hc
  · rw [hS3acc]; exact t2
  · omega
  · rw [hsp]; omega
  · rw [hS3acc]; exact t5
  · -- GuardOK
    unfold GuardOK
    have hg : S3.mem.readLE ((S3.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
      rw [hr28]
      exact hio _ _ e11 (by simp only [outside_cons, outside_nil, and_true]; omega)
    refine ⟨by rw [hr28]; exact e6, ?_, ?_⟩
    · rw [hr28, hS3acc]; exact e7
    · rw [hg, hsp]; omega
  · -- StackOK
    unfold StackOK
    refine ⟨by omega, by omega, by omega, ?_⟩
    rw [hsp, hS3acc]
    exact Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)
  · simp only [Disjoint]; omega
  · simp only [Disjoint]; rw [hsp]; omega
  · simp only [Disjoint]; rw [hsp]; omega
  · simp only [Disjoint]; omega
  · simp only [Disjoint]; rw [hsp]; omega
  · intro e he
    have hb := errAddrOf_bounds e
    rw [hio _ _ (Outside.of_sub t7 (by omega) (by omega)) (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact t8 e he

theorem hex_post {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s S3 s' : State} {M0 m : Janus.Arm64.Memory} {r0 r1 : BitVec 64} {v29 ra : Nat}
    (hpre : PreU C sb st R R2 T b L lo hi z pI nI s) (henv : HexEnv R lo hi z s) (hn2 : 2 ≤ nI.toNat)
    (hP : SbPost R st b L s pI nI r0 r1 M0 m (s.sp.toNat - 72))
    (hM0c : M0 = (((s.mem.writeLE (s.sp.toNat - 112) 8 ra).writeLE (s.sp.toNat - 120) 8 v29).writeLE (s.sp.toNat + 16) 8 pI.toNat).writeLE
      (s.sp.toNat + 8) 8 z.toNat)
    (hr0 : S3.regs 0 = BitVec.ofNat 64 (m.readLE (s.sp.toNat + 8) 8)) (hr1 : S3.regs 1 = r0) (hr2 : S3.regs 2 = r1)
    (hsp3 : S3.sp = s.sp - 112#64) (hr28 : S3.regs 28 = s.regs 28)
    (h30a : (S3.regs 30).toNat % 4 = 0) (h30b : (S3.regs 30).toNat < 2 ^ 48)
    (hS3 : S3.mem = m)
    (hq : FromHexPost z r0 nI S3 s') :
    ((∀ v, parseHex (bytesAt s.mem pI.toNat) nI.toNat = .ok v →
        s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
      (∀ e, parseHex (bytesAt s.mem pI.toNat) nI.toNat = .error e →
        s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
        s'.regs 1 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8))) ∧
    MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)]) ∧
    (s'.mem.readLE (s.sp.toNat - 112) 8 = ra % 2 ^ 64 ∧ s'.mem.readLE (s.sp.toNat - 120) 8 = v29 % 2 ^ 64) := by
  obtain ⟨-, hbytes, hF⟩ := hex_call_pre C hpre henv hn2 hP hM0c hr0 hr1 hr2 hsp3 hr28 h30a h30b hS3
  obtain ⟨-, -, -, -, -, -, cMF, hok, herr⟩ := hq
  have hp := hpre.toS
  have hlo4 := hp.lo4
  have hhi4 := hp.hi4
  have hzw := hp.zwin
  have hEnv := hp.env
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := henv
  have hsp : S3.sp.toNat = s.sp.toNat - 112 := by
    rw [hsp3]; have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [hsp] at cMF
  have hio : ∀ a n, Outside a n R.rt → Outside a n [(lo, hi)] → S3.mem.readLE a n = s.mem.readLE a n :=
    fun a n h1 h2 => hF.readLE a n (by rw [outside_append]; exact ⟨h1, h2⟩)
  have hdp : parseHex (bytesAt S3.mem r0.toNat) nI.toNat = parseHex (bytesAt s.mem pI.toNat) nI.toNat :=
    parseHex_congr _ _ _ (fun k hk => hbytes k hk)
  have hMFof : MemFrame M0 m (R.rt ++ [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8),
      (s.sp.toNat - 112 + 8, s.sp.toNat - 112 + 8 + 24)] ++ [(s.sp.toNat - 72, s.sp.toNat - 72 + 32)]) := by
    obtain ⟨hMF, -, -, -, -⟩ := hP
    have hne : s.sp.toNat - 72 ≠ 0 := by omega
    rw [if_neg hne] at hMF
    exact hMF
  have hrr := ret_reads (R := R) (buf := s.sp.toNat - 72) (by omega) (by omega) hlo4 hhi4 e9 hM0c hMFof
  rw [← hS3] at hrr
  have fin : MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)]) ∧
      (s'.mem.readLE (s.sp.toNat - 112) 8 = ra % 2 ^ 64 ∧ s'.mem.readLE (s.sp.toNat - 120) 8 = v29 % 2 ^ 64) := by
    refine ⟨hF.trans cMF ?_, ?_⟩
    · intro a n h
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
      refine ⟨⟨h1, h3⟩, h4, ?_, ?_⟩ <;> omega
    · have c1 := cMF.readLE (s.sp.toNat - 112) 8 (by
        simp only [outside_cons, outside_nil, and_true]; omega)
      have c2 := cMF.readLE (s.sp.toNat - 120) 8 (by
        simp only [outside_cons, outside_nil, and_true]; omega)
      exact ⟨by rw [c1]; exact hrr.1, by rw [c2]; exact hrr.2⟩
  refine ⟨⟨fun v h => ?_, fun e h => ?_⟩, fin⟩
  · rw [← hdp] at h; exact hok v h
  · rw [← hdp] at h
    obtain ⟨c0, c1⟩ := herr e h
    have hb := errAddrOf_bounds e
    have t6' := t6
    simp only [outside_cons, outside_nil, and_true] at t6'
    refine ⟨?_, ?_⟩
    · rw [c0, hio _ _ (Outside.of_sub t7 (by omega) (by omega)) (by simp only [outside_cons, outside_nil, and_true]; omega)]
    · rw [c1, hio _ _ (Outside.of_sub t7 (by omega) (by omega)) (by simp only [outside_cons, outside_nil, and_true]; omega)]

/-- the instance of the `fromHex` summary for the copy -/
theorem hex_inst {P : Janus.Program} {entry : Nat} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {z pI nI r0 r1 : BitVec 64}
    {s : State} {M0 m : Janus.Arm64.Memory} {st : Nat}
    (_hP : SbPost R st b L s pI nI r0 r1 M0 m (s.sp.toNat - 72))
    (hhex : ∀ (z hp len : BitVec 64), Summary P entry (FromHexPre z hp len) (FromHexPost z hp len)) :
    Summary P entry (FromHexPre z r0 nI) (FromHexPost z r0 nI) := hhex z r0 nI

/-- the byte-compare facts of the engine's branches, as `IsHex` / its negation -/
theorem hb_eq (x c : Nat) (hx : x < 256) (hc : c < 256) :
    (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 x))) - BitVec.ofNat 8 c = 0#8) ↔ x = c := by
  have h1 : BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 x))) = BitVec.ofNat 8 x := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [h1]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
    omega
  · rintro rfl
    simp

end Fv256.Arm64.UnmarshalHex
