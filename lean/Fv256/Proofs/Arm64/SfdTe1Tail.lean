import Fv256.Proofs.Arm64.SfdTe1Conv

/-!
# `strconv.toError`, write-barrier branch (arm64): the tail from the entry of `gcWriteBarrier2`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.Arm64.SfdEnv

namespace Fv256.Arm64.SfdToError

theorem rd5 {M m5 : Memory} {rt : List (Nat × Nat)} {lo hi a n t fl : Nat}
    (hMF : MemFrame (M.writeLE (t + 8) 8 fl) m5 (rt ++ [(lo, hi)]))
    (h1 : Outside a n rt) (h2 : a + n ≤ lo ∨ hi ≤ a) :
    m5.readLE a n = (M.writeLE (t + 8) 8 fl).readLE a n := by
  rw [hMF.readLE _ _ (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨h1, h2⟩)]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem pre1_vals {R : RtInv} {R2 : IfaceModel} {b : Nat} {L : List (Nat × Nat)} {fp fl sp sl : BitVec 64}
    {s S : State} {m' m2 m3 m4 : Janus.Arm64.Memory} {q t : BitVec 64}
    (F : Pre1 R R2 b L fp fl sp sl s S m' m2 m3 m4 q t) :
    m4.readLE (s.sp.toNat - 24) 8 = q.toNat ∧ m4.readLE (s.sp.toNat - 40) 8 = sl.toNat ∧
    m4.readLE (s.sp.toNat + 8) 8 = fp.toNat ∧ m4.readLE strconvErrSyntax 8 = s.mem.readLE strconvErrSyntax 8 ∧
    m4.readLE (strconvErrSyntax + 8) 8 = s.mem.readLE (strconvErrSyntax + 8) 8 ∧
    S.mem.readLE (s.sp.toNat - 104) 8 = (s.regs 29).toNat := by
  obtain ⟨hdep, hlow, e9, e10, hSf, hfr, hMF1, hMF2, hMF3, hLF1, hLF3, hCop, hinvN, hInR, hInT, hApL, hApT, hQsl, hspR, hspP,
    hsdisj, hSm8, oE, pE, qE, hf4, hacc4, hacc4t, hacc4e, hacc4w, hlr4, hfp4, hts4, hte4, hwF, hL18, hrt0, hal, hsp72, e5, pW, qW, hSrec, oW⟩ := F
  have hwin : ∀ a n, s.sp.toNat - 4192 ≤ a → a + n ≤ s.sp.toNat + 72 → Outside a n R.rt ∧ Outside a n R2.priv :=
    fun a n h1 h2 => ⟨Outside.of_sub e9 (by te_omega) (by te_omega), Outside.of_sub e10 (by te_omega) (by te_omega)⟩
  have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  have qlt : q.toNat < 2 ^ 64 := q.isLt
  have he0 : ∀ a, (a = strconvErrSyntax ∨ a = strconvErrSyntax + 8) → m4.readLE a 8 = s.mem.readLE a 8 := by
    intro a ha
    have hao : Outside a 8 [(s.sp.toNat - 4192, s.sp.toNat + 72)] := by
      rcases ha with rfl | rfl <;> exact Outside.of_sub oE (by te_omega) (by te_omega)
    have hap : Outside a 8 R.rt := by
      rcases ha with rfl | rfl <;> exact Outside.of_sub pE (by te_omega) (by te_omega)
    have hapr : Outside a 8 R2.priv := by
      rcases ha with rfl | rfl <;> exact Outside.of_sub qE (by te_omega) (by te_omega)
    simp only [outside_cons, outside_nil, and_true] at hao
    rw [te0_lrS hfr hMF1 hMF2 hMF3 hdep hlow hInR hQsl _ _ hap hapr (by te_omega) (by te_omega) (by te_omega)
      (by te_omega) (by te_omega)]
    exact hSf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; te_omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hMF3.readLE _ _ (by
          simp only [calleeStack, outside_append, outside_cons, outside_nil, and_true]
          (repeat' apply And.intro) <;> first | exact (hwin _ _ (by te_omega) (by te_omega)).1 | te_omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
    rw [h8]; exact Nat.mod_eq_of_lt qlt
  · rw [hMF3.readLE _ _ (by
          simp only [calleeStack, outside_append, outside_cons, outside_nil, and_true]
          (repeat' apply And.intro) <;> first | exact (hwin _ _ (by te_omega) (by te_omega)).1 | te_omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [h8]; exact Nat.mod_eq_of_lt sl.isLt
  · rw [te0_lrS hfr hMF1 hMF2 hMF3 hdep hlow hInR hQsl _ _ (hwin _ _ (by te_omega) (by te_omega)).1
      (hwin _ _ (by te_omega) (by te_omega)).2 (by te_omega) (by te_omega) (by te_omega) (by te_omega) (by te_omega)]
    exact hSm8
  · exact he0 _ (Or.inl rfl)
  · exact he0 _ (Or.inr rfl)
  · have h104 : s.sp.toNat - 96 - 8 = s.sp.toNat - 104 := by omega
    rw [h104] at hfp4
    rw [← hfp4, te0_lrS hfr hMF1 hMF2 hMF3 hdep hlow hInR hQsl _ _ (hwin _ _ (by te_omega) (by te_omega)).1
      (hwin _ _ (by te_omega) (by te_omega)).2 (by te_omega) (by te_omega) (by te_omega) (by te_omega) (by te_omega)]

theorem rd5b {M m5 : Memory} {rt : List (Nat × Nat)} {lo hi a n t fl : Nat}
    (hMF : MemFrame (M.writeLE (t + 8) 8 fl) m5 (rt ++ [(lo, hi)]))
    (h1 : Outside a n rt) (h2 : a + n ≤ lo ∨ hi ≤ a) (h3 : a + n ≤ t + 8 ∨ t + 16 ≤ a) :
    m5.readLE a n = M.readLE a n := by
  rw [rd5 hMF h1 h2]
  exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ h3

theorem arith_acc (r : Nat) (h : 4192 ≤ r) :
    r - 4192 ≤ r - 96 - 4096 ∧ r - 96 - 4096 + 4104 ≤ r - 4192 + (r + 72 - (r - 4192)) := by omega

theorem arith_sp (r : Nat) (h : 4192 ≤ r) : (s : BitVec 64) → s.toNat = r → (s - 96#64).toNat = r - 96 := by
  intro s hs; rw [BitVec.toNat_sub]; simp; omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem te_tail1 (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (b : Nat) (L : List (Nat × Nat))
    (fp fl sp sl : BitVec 64) (s S St : State) (m' m2 m3 m4 : Janus.Arm64.Memory) (q t : BitVec 64)
    (hwb1 : WbLiveContract (P.link impl) (P.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (P.link impl) (P.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hpc : St.pc = BitVec.ofNat 64 (te + 0xd8)) (h0 : St.regs 0 = t)
    (hmem : St.mem = m4.writeLE (t.toNat + 8) 8 fl.toNat) (h27 : St.regs 27 = 1978368#64) (hsp : St.sp = s.sp - 96#64)
    (h28 : St.regs 28 = s.regs 28) (h18 : St.regs 18 = s.regs 18)
    (hok1 : R.ok (P.contractAddr "runtime.gcWriteBarrier1") [1]) (hok2 : R.ok (P.contractAddr "runtime.gcWriteBarrier2") [2])
    (hl1 : (s.regs 30).toNat % 4 = 0) (hl2 : (s.regs 30).toNat < 2 ^ 48)
    (F : Pre1 R R2 b L fp fl sp sl s S m' m2 m3 m4 q t) :
    ReachesRet (P.link impl) (s.regs regLR) St (TePost R R2 b L fp fl sp sl s) := by
  have hv := pre1_vals F
  have F0 := F
  obtain ⟨hdep, hlow, e9, e10, hSf, hfr, hMF1, hMF2, hMF3, hLF1, hLF3, hCop, hinvN, hInR, hInT, hApL, hApT, hQsl, hspR, hspP,
    hsdisj, hSm8, oE, pE, qE, hf4, hacc4, hacc4t, hacc4e, hacc4w, hlr4, hfp4, hts4, hte4, hwF, hL18, hrt0, hal, hsp72, e5, pW, qW, hSrec, oW⟩ := F
  have hsp0 : (s.sp - 96#64).toNat = s.sp.toNat - 96 := arith_sp _ hlow _ rfl
  have hSN : St.sp.toNat = s.sp.toNat - 96 := by rw [hsp]; exact hsp0
  have hqw := InRanges.disjoint hInR e9
  have hSacc : s.mem.accessible (s.sp.toNat - 96 - 4096) 4104 true = true := by
    exact Memory.accessible_mono _ e5 (arith_acc _ hlow).1 (arith_acc _ hlow).2
  have ht48 : t.toNat + 48 ≤ 2 ^ 48 := Memory.accessible_bound _ hacc4t
  have hf4l : m4.readLE 1979584 4 ≠ 0 := hf4
  have hacc4l : m4.accessible 1979584 4 false = true := hacc4
  have hwFl : 1979584 + 4 ≤ t.toNat ∨ t.toNat + 48 ≤ 1979584 := hwF
  janus_run [hmem, h0, h27, hsp, hf4l, hacc4l] until [te + 0xf0] calls [hw2 := hwb2]
  obtain ⟨buf, junk, f, v, m5, ex, ep, hs', hMF, hLF, hSl, hApLq, hApW, hIS⟩ := hw2
  have key : ∀ X, X = wbRetX { St with regs := setReg (setReg St.regs 1 (BitVec.ofNat 64 (m4.readLE 1979584 4))) 30 618880#64 }
      junk buf f v m5 ex ep → ReachesRet (P.link impl) (s.regs regLR) X (TePost R R2 b L fp fl sp sl s) := by
    intro X hX; subst hX
    have hwb : wbFlag = 1979584 := by decide
    have hes : strconvErrSyntax = 1793712 := by decide
    have hwin : ∀ a n, s.sp.toNat - 4192 ≤ a → a + n ≤ s.sp.toNat + 72 → Outside a n R.rt := fun a n h1 h2 =>
      Outside.of_sub e9 (by te_omega) (by te_omega)
    have hts5 : s.sp.toNat + 72 ≤ t.toNat ∨ t.toNat + 48 ≤ s.sp.toNat - 4192 := by
      have := hts4; te_omega
    have hf5 : m5.readLE 1979584 4 ≠ 0 := by
      rw [← hwb, rd5b hMF pW (by simp only [outside_cons, outside_nil, and_true] at oW; te_omega) (by simp only [hwb] at hwF; te_omega)]
      exact hf4
    have hlr5 : m5.readLE (s.sp.toNat - 96) 8 = (s.regs 30).toNat := by
      rw [rd5b hMF (hwin _ _ (by te_omega) (by te_omega)) (by te_omega) (by te_omega)]; exact hlr4
    have hfp5 : m5.readLE (s.sp.toNat - 96 - 8) 8 = (s.regs 29).toNat := by
      rw [rd5b hMF (hwin _ _ (by te_omega) (by te_omega)) (by te_omega) (by te_omega)]; exact hfp4
    have hfn5 : m5.readLE (s.sp.toNat + 8) 8 = fp.toNat := by
      rw [rd5b hMF (hwin _ _ (by te_omega) (by te_omega)) (by te_omega) (by te_omega)]; exact hv.2.2.1
    have hq5 : m5.readLE (s.sp.toNat - 24) 8 = q.toNat := by
      rw [rd5b hMF (hwin _ _ (by te_omega) (by te_omega)) (by te_omega) (by te_omega)]; exact hv.1
    have hsl5 : m5.readLE (s.sp.toNat - 40) 8 = sl.toNat := by
      rw [rd5b hMF (hwin _ _ (by te_omega) (by te_omega)) (by te_omega) (by te_omega)]; exact hv.2.1
    have hoEl : 1793712 + 16 ≤ s.sp.toNat - 4192 ∨ s.sp.toNat + 72 ≤ 1793712 := by
      have := oE; simp only [outside_cons, outside_nil, and_true] at this; rw [hes] at this; exact this
    have hteEl : 1793712 + 16 ≤ t.toNat ∨ t.toNat + 48 ≤ 1793712 := by
      have := hte4; rw [hes] at this; exact this
    have hes8 : strconvErrSyntax + 8 = 1793720 := by decide
    have hE50 : m5.readLE 1793712 8 = s.mem.readLE strconvErrSyntax 8 := by
      rw [rd5b hMF (by rw [← hes]; exact Outside.of_sub pE (by te_omega) (by te_omega)) (by te_omega) (by te_omega), ← hes]
      exact hv.2.2.2.1
    have hE51 : m5.readLE 1793720 8 = s.mem.readLE (strconvErrSyntax + 8) 8 := by
      rw [rd5b hMF (by rw [← hes8]; exact Outside.of_sub pE (by te_omega) (by te_omega)) (by te_omega) (by te_omega), ← hes8]
      exact hv.2.2.2.2.1
    obtain ⟨hBin, hBle, hBacc, hBal⟩ := hSl
    have hBin16 : InRanges buf.toNat 16 R.rt := hBin
    have hAfl : Apart 1979584 4 buf.toNat 16 := InRanges.apart hBin16 (by rw [← hwb]; exact pW)
    have hAwin : Apart (s.sp.toNat - 4192) (s.sp.toNat + 72 - (s.sp.toNat - 4192)) buf.toNat 16 := InRanges.apart hBin16 e9
    have hAe : Apart 1793712 16 buf.toNat 16 := InRanges.apart hBin16 (by rw [← hes]; exact pE)
    have hAt : Apart buf.toNat 16 t.toNat 48 := hApLq.2
    simp only [Apart] at hAfl hAwin hAe hAt
    janus_run [hf5, hlr5, hfp5, hfn5, hq5, hsl5, hE50, hE51, hBle] calls [hw1 := hwb1]
    refine te1_conv F0 hMF hLF hBin16 hAt (hApLq.1.2) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    · assumption
    · assumption
    · assumption
    · assumption
    · assumption
    · rfl
    · simp [wbRegs_apply, setReg_apply]
      rw [hv.2.2.2.2.2]; simp
    · simp [wbRegs_apply, setReg_apply, h28]
    · simp [wbRegs_apply, setReg_apply, h18]
    · simp [wbRegs_apply, setReg_apply]
    · simp [wbRegs_apply, setReg_apply]
  exact key _ (by simp only [wbRetX, hsp, setReg_apply] at hs' ⊢; exact hs')

end Fv256.Arm64.SfdToError
