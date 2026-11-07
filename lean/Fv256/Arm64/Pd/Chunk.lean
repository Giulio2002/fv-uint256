import Fv256.Arm64.PrettyProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.PdCells
import Fv256.Arm64.P.T
import Fv256.Util
import Fv256.UtilB2
import Fv256.Arm64.Pd.Iter1
import Fv256.Arm64.Pd.Inner
import Fv256.Arm64.Pd.Pad
import Fv256.Arm64.Pd.Tail

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec
open Fv256.E Fv256.Arm64.P

namespace Fv256.Arm64.Pd

theorem wv_frame {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) (p : Nat) (ho : Outside p 32 rs) :
    Fv256.B.wv m' p 4 = Fv256.B.wv m p 4 := by
  rw [Fv256.B.wv4_eq, Fv256.B.wv4_eq]; exact h.readLE p 32 ho

theorem digits_shift (z D0 k : Nat) : z / 10 ^ D0 / 10 ^ k = z / 10 ^ (D0 + k) := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- One chunk up to the end of the inner copy loop (`pdJ`). `D0` digits are done; `y = z / 10^D0` is the current quotient. -/
theorem pd_chunk_core (s : State) (b z D0 sepb : Nat) (M : Memory) (hpc : s.pc = BitVec.ofNat 64 pdH) (hM : s.mem = M)
    (hy0 : z / 10 ^ D0 ≠ 0) (hz1 : z < 2 ^ 256) (hD0 : D0 ≤ 76) (hsb : sepb < 256)
    (hb : 368 ≤ b) (hb16 : b % 16 = 0) (hb2 : b + 424 ≤ 2 ^ 48)
    (hw : M.accessible (b - 368) (368 + 424) true = true)
    (hd : TabsOK M)
    (esp : s.sp = BitVec.ofNat 64 b)
    (e0 : s.regs 0 = 19#64) (e2 : s.regs 2 = BitVec.ofNat 64 (132 - cOf D0)) (e3 : s.regs 3 = BitVec.ofNat 64 (b + 320))
    (e4 : s.regs 4 = BitVec.ofNat 64 (cOf D0 % 4)) (e6 : s.regs 6 = BitVec.ofNat 64 (b + 352))
    (e8 : s.regs 8 = BitVec.ofNat 64 (b + 80))
    (hg3 : M.readLE ((s.regs 28).toNat + 16) 8 + 304 < b) (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48)
    (hg2 : M.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hgd : (s.regs 28).toNat + 16 + 8 ≤ b - 368 ∨ b + 424 ≤ (s.regs 28).toNat + 16)
    (hym : Fv256.B.wv M (b + 320) 4 = z / 10 ^ D0) (hdm : Fv256.B.wv M (b + 352) 4 = 10 ^ 19)
    (hsep : M.readLE (b + 416) 1 = sepb) (hout : OutIs M (b + 231) sepb z (cOf D0)) :
    ReachesRet Fv256.Arm64.PrettyProg.program (BitVec.ofNat 64 pdJ) s
      (fun S' => S'.regs 0 = BitVec.ofNat 64 (b + 80) ∧ S'.regs 1 = BitVec.ofNat 64 (decLen (z / 10 ^ D0 % 10 ^ 19)) ∧
        S'.regs 2 = 19#64 ∧ S'.sp = s.sp ∧ S'.regs 9 = BitVec.ofNat 64 sepb ∧
        S'.regs 10 = BitVec.ofNat 64 (132 - cOf (D0 + decLen (z / 10 ^ D0 % 10 ^ 19))) ∧
        S'.regs 11 = BitVec.ofNat 64 (cOf (D0 + decLen (z / 10 ^ D0 % 10 ^ 19)) % 4) ∧
        S'.regs 28 = s.regs 28 ∧ S'.regs 29 = s.regs 29 ∧ S'.regs 18 = s.regs 18 ∧
        Fv256.B.wv S'.mem (b + 320) 4 = z / 10 ^ D0 / 10 ^ 19 ∧ Fv256.B.wv S'.mem (b + 352) 4 = 10 ^ 19 ∧
        S'.mem.readLE (b + 416) 1 = sepb ∧
        MemFrame M S'.mem [(b - 368, b - 8), (b + 8, b + 392)] ∧
        OutIs S'.mem (b + 231) sepb z (cOf (D0 + decLen (z / 10 ^ D0 % 10 ^ 19))) ∧ TabsOK S'.mem) := by
  have hy1 : z / 10 ^ D0 < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hz1
  have hcD0 : cOf D0 ≤ 132 := by
    have := cOf_mono D0 76 hD0
    have h76 : cOf 76 = 101 := by decide
    omega
  refine Fv256.E.reachesRet64_bind (pd_iter1 s b (cOf D0) (z / 10 ^ D0) sepb M hpc hM hy0 hy1 hcD0 hsb hb hb16 hb2 hw hd esp
    e0 e2 e3 e4 e6 e8 hg3 hg1 hg2 hgd hym hdm hsep) ?_
  intro S1 hrip ⟨r0, r1, r2, r8, r9, r10, r11, r28, r29, r18, rsp, ry, rd, rdig, rsep, rfr, rtab⟩
  have hrlt : z / 10 ^ D0 % 10 ^ 19 < 10 ^ 19 := Nat.mod_lt _ (by decide)
  have hnd19 : decLen (z / 10 ^ D0 % 10 ^ 19) ≤ 19 := decLen_le_of_lt_pow _ 19 (by decide) hrlt
  have hnd1 := decLen_pos (z / 10 ^ D0 % 10 ^ 19)
  generalize hndd : decLen (z / 10 ^ D0 % 10 ^ 19) = nd at hnd19 hnd1 r1 r8 r10 r11 rdig ⊢
  have hcb : cOf (D0 + nd) ≤ 132 := by
    have := cOf_mono (D0 + nd) 95 (by omega)
    have h95 : cOf 95 = 126 := by decide
    omega
  have hwaS : S1.mem.accessible (b - 368) (368 + 424) true = true := by rw [rfr.accessible]; exact hw
  have hout1 : OutIs S1.mem (b + 231) sepb z (cOf D0) :=
    OutIs.of_agree hout (by omega) (fun p hp => rfr.readLE _ _ (by simp only [Outside, and_true]; omega))
  have hdig' : ∀ j, j < nd → S1.mem.readLE (b + 80 + j) 1 = 48 + z / 10 ^ (D0 + nd - 1 - j) % 10 := by
    intro j hj
    have := rdig (nd - 1 - j) (by omega)
    rw [show b + 80 + nd - 1 - (nd - 1 - j) = b + 80 + j by omega, digits_shift] at this
    rw [this, show D0 + nd - 1 - j = D0 + (nd - 1 - j) by omega]
  have e8' : S1.regs 8 = BitVec.ofNat 64 nd - 1#64 := by
    rw [r8]; exact (Fv256.E.ofNat_sub_ofNat nd 1 (by omega) (by omega)).symm
  have esp1 : S1.sp = BitVec.ofNat 64 b := by rw [rsp]; exact esp
  refine Fv256.E.reachesRet64_mono (pd_inner_loop b D0 nd sepb z hsb hb hb2 hnd19 hcb nd (Nat.le_refl _) S1 hrip
    (accessible_sub hwaS (Or.inr rfl) (by omega) (by omega)) (accessible_sub hwaS (Or.inr rfl) (by omega) (by omega))
    r0 e8' esp1 r9 (by rw [r10, Nat.add_sub_cancel]) (by rw [r11, Nat.add_sub_cancel]) hdig' (by rw [Nat.add_sub_cancel]; exact hout1)) ?_
  rintro S ⟨qk, q10, q11, qsp, qfr, qout⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, q10, q11, ?_, ?_, ?_, ?_, ?_, ?_, ?_, qout, ?_⟩
  · rw [qk 0 (by simp)]; exact r0
  · rw [qk 1 (by simp)]; exact r1
  · rw [qk 2 (by simp)]; exact r2
  · rw [qsp]; exact rsp
  · rw [qk 9 (by simp)]; exact r9
  · rw [qk 28 (by simp)]; exact r28
  · rw [qk 29 (by simp)]; exact r29
  · rw [qk 18 (by simp)]; exact r18
  · rw [wv_frame qfr _ (by simp only [Outside, and_true]; omega)]; exact ry
  · rw [wv_frame qfr _ (by simp only [Outside, and_true]; omega)]; exact rd
  · rw [qfr.readLE _ _ (by simp only [Outside, and_true]; omega)]; exact rsep
  · exact MemFrame.trans (rs := [(b - 368, b - 8), (b + 8, b + 392)]) (rs' := [(b - 368, b - 8), (b + 8, b + 392)]) (rfr.mono (by
      intro a n h; simp only [Outside, and_true] at h ⊢; omega)) (qfr.mono (by
      intro a n h; simp only [Outside, and_true] at h ⊢; omega)) (fun a n h => ⟨h, h⟩)
  · refine rtab.frame qfr ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact accessible_sub hwaS (Or.inr rfl) (by omega) (by omega)

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- A non-final chunk (`z / 10^(D0+19) ≠ 0`): back to the loop head with `D0 + 19` digits done. -/
theorem pd_chunk_next (s : State) (b z D0 sepb : Nat) (M : Memory) (hpc : s.pc = BitVec.ofNat 64 pdH) (hM : s.mem = M)
    (hy0 : z / 10 ^ D0 ≠ 0) (hy' : z / 10 ^ (D0 + 19) ≠ 0) (hz1 : z < 2 ^ 256) (hD0 : D0 ≤ 76) (hsb : sepb < 256)
    (hb : 368 ≤ b) (hb16 : b % 16 = 0) (hb2 : b + 424 ≤ 2 ^ 48)
    (hw : M.accessible (b - 368) (368 + 424) true = true)
    (hd : TabsOK M)
    (esp : s.sp = BitVec.ofNat 64 b)
    (e0 : s.regs 0 = 19#64) (e2 : s.regs 2 = BitVec.ofNat 64 (132 - cOf D0)) (e3 : s.regs 3 = BitVec.ofNat 64 (b + 320))
    (e4 : s.regs 4 = BitVec.ofNat 64 (cOf D0 % 4)) (e6 : s.regs 6 = BitVec.ofNat 64 (b + 352))
    (e8 : s.regs 8 = BitVec.ofNat 64 (b + 80))
    (hg3 : M.readLE ((s.regs 28).toNat + 16) 8 + 304 < b) (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48)
    (hg2 : M.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hgd : (s.regs 28).toNat + 16 + 8 ≤ b - 368 ∨ b + 424 ≤ (s.regs 28).toNat + 16)
    (hym : Fv256.B.wv M (b + 320) 4 = z / 10 ^ D0) (hdm : Fv256.B.wv M (b + 352) 4 = 10 ^ 19)
    (hsep : M.readLE (b + 416) 1 = sepb) (hout : OutIs M (b + 231) sepb z (cOf D0)) :
    ReachesRet Fv256.Arm64.PrettyProg.program (BitVec.ofNat 64 pdH) s
      (fun S' => S'.regs 0 = 19#64 ∧ S'.regs 2 = BitVec.ofNat 64 (132 - cOf (D0 + 19)) ∧
        S'.regs 8 = BitVec.ofNat 64 (b + 80) ∧ S'.regs 4 = BitVec.ofNat 64 (cOf (D0 + 19) % 4) ∧
        S'.regs 3 = BitVec.ofNat 64 (b + 320) ∧ S'.regs 6 = BitVec.ofNat 64 (b + 352) ∧
        S'.sp = s.sp ∧ S'.regs 28 = s.regs 28 ∧ S'.regs 29 = s.regs 29 ∧ S'.regs 18 = s.regs 18 ∧
        Fv256.B.wv S'.mem (b + 320) 4 = z / 10 ^ (D0 + 19) ∧ Fv256.B.wv S'.mem (b + 352) 4 = 10 ^ 19 ∧
        S'.mem.readLE (b + 416) 1 = sepb ∧
        MemFrame M S'.mem [(b - 368, b - 8), (b + 8, b + 392)] ∧ OutIs S'.mem (b + 231) sepb z (cOf (D0 + 19)) ∧ TabsOK S'.mem) := by
  have hrlt : z / 10 ^ D0 % 10 ^ 19 < 10 ^ 19 := Nat.mod_lt _ (by decide)
  have hnd19 : decLen (z / 10 ^ D0 % 10 ^ 19) ≤ 19 := decLen_le_of_lt_pow _ 19 (by decide) hrlt
  have hnd1 := decLen_pos (z / 10 ^ D0 % 10 ^ 19)
  have hlt := decLen_lt_pow (z / 10 ^ D0 % 10 ^ 19)
  refine Fv256.E.reachesRet64_bind (pd_chunk_core s b z D0 sepb M hpc hM hy0 hz1 hD0 hsb hb hb16 hb2 hw hd esp e0 e2 e3 e4 e6 e8
    hg3 hg1 hg2 hgd hym hdm hsep hout) ?_
  intro S1 hrip ⟨r0, r1, r2, rsp, r9, r10, r11, r28, r29, r18, ry, rd, rsep, rfr, rout, rtab⟩
  generalize hndd : decLen (z / 10 ^ D0 % 10 ^ 19) = nn at hnd19 hnd1 hlt r1 r10 r11 rout
  have hwaS : S1.mem.accessible (b - 368) (368 + 424) true = true := by rw [rfr.accessible]; exact hw
  have hy1 : z / 10 ^ D0 / 10 ^ 19 ≠ 0 := by rw [digits_shift]; exact hy'
  have hpadz : ∀ i, D0 + nn ≤ i → i < D0 + 19 → z / 10 ^ i % 10 = 0 := by
    intro i hi1 hi2
    have h1 : z / 10 ^ D0 % 10 ^ 19 < 10 ^ (i - D0) :=
      Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : z / 10 ^ D0 % 10 ^ 19 / 10 ^ (i - D0) = 0 := Nat.div_eq_of_lt h1
    have h3 := Fv256.E.digit_mod (z / 10 ^ D0) (i - D0) 19 (by omega)
    rw [h2, digits_shift, show D0 + (i - D0) = i by omega] at h3
    omega
  have hcb : cOf (D0 + 19) ≤ 132 := by
    have := cOf_mono (D0 + 19) 95 (by omega)
    have h95 : cOf 95 = 126 := by decide
    omega
  have esp1 : S1.sp = BitVec.ofNat 64 b := by rw [rsp]; exact esp
  refine Fv256.E.reachesRet64_bind (pd_tail_nz S1 b (z / 10 ^ D0 / 10 ^ 19) hrip esp1 hb hb16 hb2
    (by rw [rfr.accessible]; exact accessible_sub hw (Or.inr rfl) (by omega) (by omega)) ry hy1) ?_
  intro S2 hrip2 ⟨t3, tsp, tk, tm⟩
  refine Fv256.E.reachesRet64_mono (pd_pad_loop b D0 nn sepb z hsb hb hb2 hnd1 hnd19 hcb hpadz (19 - nn) (Nat.le_refl _) S2 hrip2
    (by rw [tm, rfr.accessible]; exact accessible_sub hw (Or.inr rfl) (by omega) (by omega))
    (by rw [t3]; simp) (by rw [tk 1 (by simp)]; exact r1) (by rw [tsp]; exact esp1) (by rw [tk 9 (by simp)]; exact r9)
    (by rw [tk 10 (by simp), r10, show D0 + 19 - (19 - nn) = D0 + nn by omega])
    (by rw [tk 11 (by simp), r11, show D0 + 19 - (19 - nn) = D0 + nn by omega])
    (by rw [tm, show D0 + 19 - (19 - nn) = D0 + nn by omega]; exact rout)) ?_
  rintro S ⟨q0, q2, q8, q4, q3, q6, qsp, qk, qfr0, qout⟩
  have qfr : MemFrame S1.mem S.mem [(b + 99, b + 232)] := by rw [← tm]; exact qfr0
  refine ⟨?_, q2, ?_, q4, q3, q6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, qout, ?_⟩
  · rw [q0, tk 2 (by simp)]; exact r2
  · rw [q8, tk 0 (by simp)]; exact r0
  · rw [qsp, tsp, rsp]
  · rw [qk 28 (by simp), tk 28 (by simp)]; exact r28
  · rw [qk 29 (by simp), tk 29 (by simp)]; exact r29
  · rw [qk 18 (by simp), tk 18 (by simp)]; exact r18
  · rw [wv_frame qfr _ (by simp only [Outside, and_true]; omega), ry, digits_shift]
  · rw [wv_frame qfr _ (by simp only [Outside, and_true]; omega)]; exact rd
  · rw [qfr.readLE _ _ (by simp only [Outside, and_true]; omega)]; exact rsep
  · exact MemFrame.trans (rs := [(b - 368, b - 8), (b + 8, b + 392)]) (rs' := [(b - 368, b - 8), (b + 8, b + 392)]) rfr (qfr.mono (by
      intro a n h; simp only [Outside, and_true] at h ⊢; omega)) (fun a n h => ⟨h, h⟩)
  · refine rtab.frame qfr ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact accessible_sub hwaS (Or.inr rfl) (by omega) (by omega)

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- The final chunk (`z / 10^(D0+19) = 0`): to `pdF` with all `plen z` cells produced. -/
theorem pd_chunk_final (s : State) (b z D0 sepb : Nat) (M : Memory) (hpc : s.pc = BitVec.ofNat 64 pdH) (hM : s.mem = M)
    (hy0 : z / 10 ^ D0 ≠ 0) (hy' : z / 10 ^ (D0 + 19) = 0) (hz1 : z < 2 ^ 256) (hD0 : D0 ≤ 76) (hsb : sepb < 256)
    (hb : 368 ≤ b) (hb16 : b % 16 = 0) (hb2 : b + 424 ≤ 2 ^ 48)
    (hw : M.accessible (b - 368) (368 + 424) true = true)
    (hd : TabsOK M)
    (esp : s.sp = BitVec.ofNat 64 b)
    (e0 : s.regs 0 = 19#64) (e2 : s.regs 2 = BitVec.ofNat 64 (132 - cOf D0)) (e3 : s.regs 3 = BitVec.ofNat 64 (b + 320))
    (e4 : s.regs 4 = BitVec.ofNat 64 (cOf D0 % 4)) (e6 : s.regs 6 = BitVec.ofNat 64 (b + 352))
    (e8 : s.regs 8 = BitVec.ofNat 64 (b + 80))
    (hg3 : M.readLE ((s.regs 28).toNat + 16) 8 + 304 < b) (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48)
    (hg2 : M.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hgd : (s.regs 28).toNat + 16 + 8 ≤ b - 368 ∨ b + 424 ≤ (s.regs 28).toNat + 16)
    (hym : Fv256.B.wv M (b + 320) 4 = z / 10 ^ D0) (hdm : Fv256.B.wv M (b + 352) 4 = 10 ^ 19)
    (hsep : M.readLE (b + 416) 1 = sepb) (hout : OutIs M (b + 231) sepb z (cOf D0)) :
    ReachesRet Fv256.Arm64.PrettyProg.program (BitVec.ofNat 64 pdF) s
      (fun S' => S'.regs 10 = BitVec.ofNat 64 (132 - plen z) ∧
        S'.sp = s.sp ∧ S'.regs 28 = s.regs 28 ∧ S'.regs 29 = s.regs 29 ∧ S'.regs 18 = s.regs 18 ∧
        MemFrame M S'.mem [(b - 368, b - 8), (b + 8, b + 392)] ∧ OutIs S'.mem (b + 231) sepb z (plen z) ∧ TabsOK S'.mem) := by
  have hrlt : z / 10 ^ D0 % 10 ^ 19 < 10 ^ 19 := Nat.mod_lt _ (by decide)
  have hy10 : z / 10 ^ D0 < 10 ^ 19 := by
    have := Nat.div_eq_zero_iff.mp (show z / 10 ^ D0 / 10 ^ 19 = 0 by rw [digits_shift]; exact hy')
    omega
  have h10 : 10 ^ D0 ≤ z := Nat.le_of_not_lt (fun hc => hy0 (Nat.div_eq_of_lt hc))
  have hdz : decLen z = decLen (z / 10 ^ D0) + D0 := decLen_div_pow z D0 h10
  have hnd : decLen (z / 10 ^ D0 % 10 ^ 19) = decLen (z / 10 ^ D0) := by rw [Nat.mod_eq_of_lt hy10]
  refine Fv256.E.reachesRet64_bind (pd_chunk_core s b z D0 sepb M hpc hM hy0 hz1 hD0 hsb hb hb16 hb2 hw hd esp e0 e2 e3 e4 e6 e8
    hg3 hg1 hg2 hgd hym hdm hsep hout) ?_
  intro S1 hrip ⟨r0, r1, r2, rsp, r9, r10, r11, r28, r29, r18, ry, rd, rsep, rfr, rout, rtab⟩
  have hD : D0 + decLen (z / 10 ^ D0 % 10 ^ 19) = decLen z := by rw [hnd]; omega
  rw [hD, cOf_plen] at r10 rout
  have esp1 : S1.sp = BitVec.ofNat 64 b := by rw [rsp]; exact esp
  have hy2 : z / 10 ^ D0 / 10 ^ 19 = 0 := by rw [digits_shift]; exact hy'
  refine Fv256.E.reachesRet64_mono (pd_tail_z S1 b hrip esp1 hb hb16 hb2
    (by rw [rfr.accessible]; exact accessible_sub hw (Or.inr rfl) (by omega) (by omega)) (by rw [ry, hy2])) ?_
  rintro S ⟨tsp, tk, tm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tk 10 (by simp)]; exact r10
  · rw [tsp]; exact rsp
  · rw [tk 28 (by simp)]; exact r28
  · rw [tk 29 (by simp)]; exact r29
  · rw [tk 18 (by simp)]; exact r18
  · rw [tm]; exact rfr
  · rw [tm]; exact rout
  · rw [tm]; exact rtab
end Fv256.Arm64.Pd
