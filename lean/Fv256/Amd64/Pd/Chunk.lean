import Fv256.PrettyProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.PdCells
import Fv256.Amd64.P.T
import Fv256.Util
import Fv256.UtilB2
import Fv256.Amd64.Pd.Iter1
import Fv256.Amd64.Pd.Inner
import Fv256.Amd64.Pd.Pad
import Fv256.Amd64.Pd.Tail

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E Fv256.Amd64.P

namespace Fv256.Amd64.Pd

theorem wv_frame {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) (p : Nat) (ho : Outside p 32 rs) :
    Fv256.B.wv m' p 4 = Fv256.B.wv m p 4 := by
  rw [Fv256.B.wv4_eq, Fv256.B.wv4_eq]; exact h.readLE p 32 ho

theorem digits_shift (z D0 k : Nat) : z / 10 ^ D0 / 10 ^ k = z / 10 ^ (D0 + k) := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]


set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- One chunk up to the end of the inner copy loop (`pdJ`). `D0` digits are done; `y = z / 10^D0` is the current quotient. -/
theorem pd_chunk_core (s : State) (b z D0 sepb : Nat) (M : Memory) (hpc : s.rip = BitVec.ofNat 64 pdH) (hM : s.mem = M)
    (hy0 : z / 10 ^ D0 ≠ 0) (hz1 : z < 2 ^ 256) (hD0 : D0 ≤ 76) (hsb : sepb < 256)
    (hb : 0x180 ≤ b) (hb8 : b % 8 = 0) (hb2 : b + 0x198 ≤ 2 ^ 48)
    (hw : M.accessible (b - 0x180) (0x180 + 0x198) true = true)
    (hd : TabsOK M)
    (hx15 : s.xmm 15 = 0) (hdf : s.df = false)
    (e0 : s.regs 0 = BitVec.ofNat 64 19) (e1 : s.regs 1 = BitVec.ofNat 64 (132 - cOf D0)) (e2 : s.regs 2 = BitVec.ofNat 64 (b + 0x40))
    (e6 : s.regs 6 = BitVec.ofNat 64 (cOf D0 % 4)) (e7 : s.regs 7 = BitVec.ofNat 64 (b + 0x130)) (e9 : s.regs 9 = BitVec.ofNat 64 (b + 0x150))
    (e4 : s.regs 4 = BitVec.ofNat 64 b) (e5 : s.regs 5 = BitVec.ofNat 64 (b + 0x178))
    (hg3 : M.readLE ((s.regs 14).toNat + 16) 8 + 0x100 < b) (hg1 : (s.regs 14).toNat + 24 ≤ 2 ^ 48)
    (hg2 : M.accessible ((s.regs 14).toNat + 16) 8 false = true)
    (hgd : (s.regs 14).toNat + 16 + 8 ≤ b - 0x180 ∨ b + 0x198 ≤ (s.regs 14).toNat + 16)
    (hym : Fv256.B.wv M (b + 0x130) 4 = z / 10 ^ D0) (hdm : Fv256.B.wv M (b + 0x150) 4 = 10 ^ 19)
    (hsep : M.readLE (b + 0x190) 1 = sepb) (hout : OutIs M (b + 215) sepb z (cOf D0)) :
    ReachesRet Fv256.PrettyProg.program (BitVec.ofNat 64 pdJ) s
      (fun S' => S'.regs 0 = BitVec.ofNat 64 (b + 0x40) ∧ S'.regs 1 = 19#64 ∧
        S'.regs 3 = BitVec.ofNat 64 (decLen (z / 10 ^ D0 % 10 ^ 19)) ∧ S'.regs 4 = BitVec.ofNat 64 b ∧
        S'.regs 5 = BitVec.ofNat 64 (b + 0x178) ∧ S'.regs 11 = BitVec.ofNat 64 sepb ∧
        S'.regs 12 = BitVec.ofNat 64 (132 - cOf (D0 + decLen (z / 10 ^ D0 % 10 ^ 19))) ∧
        S'.regs 13 = BitVec.ofNat 64 (cOf (D0 + decLen (z / 10 ^ D0 % 10 ^ 19)) % 4) ∧ S'.regs 14 = s.regs 14 ∧
        S'.xmm 15 = 0 ∧ S'.df = false ∧
        Fv256.B.wv S'.mem (b + 0x130) 4 = z / 10 ^ D0 / 10 ^ 19 ∧ Fv256.B.wv S'.mem (b + 0x150) 4 = 10 ^ 19 ∧
        MemFrame M S'.mem [(b - 0x180, b + 376)] ∧
        OutIs S'.mem (b + 215) sepb z (cOf (D0 + decLen (z / 10 ^ D0 % 10 ^ 19))) ∧ TabsOK S'.mem) := by
  have hy1 : z / 10 ^ D0 < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hz1
  have hcD0 : cOf D0 ≤ 132 := by
    have := cOf_mono D0 76 hD0
    have h76 : cOf 76 = 101 := by decide
    omega
  refine Fv256.E.reachesRet_bind' (pd_iter1 s b (cOf D0) (z / 10 ^ D0) sepb M hpc hM hy0 hy1 hcD0 hsb hb hb8 hb2 hw hd hx15 hdf
    e0 e1 e2 e6 e7 e9 e4 e5 hg3 hg1 hg2 hgd hym hdm hsep) ?_
  intro S1 hrip ⟨r0, r2, r3, r4, r5, r11, r12, r13, r14, rx, rdf, ry, rd, rdig, rfr, rtab, r1⟩
  have hrlt : z / 10 ^ D0 % 10 ^ 19 < 10 ^ 19 := Nat.mod_lt _ (by decide)
  have hnd19 : decLen (z / 10 ^ D0 % 10 ^ 19) ≤ 19 := decLen_le_of_lt_pow _ 19 (by decide) hrlt
  have hnd1 := decLen_pos (z / 10 ^ D0 % 10 ^ 19)
  generalize hndd : decLen (z / 10 ^ D0 % 10 ^ 19) = nd at hnd19 hnd1 r2 r3 r12 rdig ⊢
  have hcb : cOf (D0 + nd) ≤ 132 := by
    have := cOf_mono (D0 + nd) 95 (by omega)
    have h95 : cOf 95 = 126 := by decide
    omega
  have hwaS : S1.mem.accessible (b - 0x180) (0x180 + 0x198) true = true := by rw [rfr.accessible]; exact hw
  have hout1 : OutIs S1.mem (b + 215) sepb z (cOf D0) :=
    OutIs.of_agree hout (by omega) (fun p hp => rfr.readLE _ _ (by simp only [Outside, and_true]; omega))
  have hdig' : ∀ j, j < nd → S1.mem.readLE (b + 64 + j) 1 = 48 + z / 10 ^ (D0 + nd - 1 - j) % 10 := by
    intro j hj
    have := rdig (nd - 1 - j) (by omega)
    rw [show b + 0x40 + nd - 1 - (nd - 1 - j) = b + 64 + j by omega, digits_shift] at this
    rw [this, show D0 + nd - 1 - j = D0 + (nd - 1 - j) by omega]
  have e2' : S1.regs 2 = BitVec.ofNat 64 nd - 1#64 := by
    rw [r2]; exact (Fv256.E.ofNat_sub_ofNat nd 1 (by omega) (by omega)).symm
  refine ReachesRet.mono (pd_inner_loop b D0 nd sepb z hsb hb hb2 hnd19 hcb nd (Nat.le_refl _) S1 hrip
    (accessible_sub hwaS (Or.inr rfl) (by omega) (by omega)) (accessible_sub hwaS (Or.inr rfl) (by omega) (by omega))
    r0 e2' r4 r11 (by rw [r12, Nat.add_sub_cancel]) (by rw [r13, Nat.add_sub_cancel]) hdig' (by rw [Nat.add_sub_cancel]; exact hout1)) ?_
  rintro S ⟨qk, q12, q13, qx, qdf, qfr, qout⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, q12, q13, ?_, ?_, ?_, ?_, ?_, ?_, qout, ?_⟩
  · rw [qk 0 (by simp)]; exact r0
  · rw [qk 1 (by simp)]; exact r1
  · rw [qk 3 (by simp)]; exact r3
  · rw [qk 4 (by simp)]; exact r4
  · rw [qk 5 (by simp)]; exact r5
  · rw [qk 11 (by simp)]; exact r11
  · rw [qk 14 (by simp)]; exact r14
  · rw [qx]; exact rx
  · rw [qdf]; exact rdf
  · rw [wv_frame qfr _ (by simp only [Outside, and_true]; omega)]; rw [ry, digits_shift]
  · rw [wv_frame qfr _ (by simp only [Outside, and_true]; omega)]; exact rd
  · exact MemFrame.trans (rs := [(b - 0x180, b + 376)]) (rs' := [(b - 0x180, b + 376)]) (rfr.mono (by
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
theorem pd_chunk_next (s : State) (b z D0 sepb : Nat) (M : Memory) (hpc : s.rip = BitVec.ofNat 64 pdH) (hM : s.mem = M)
    (hy0 : z / 10 ^ D0 ≠ 0) (hy' : z / 10 ^ (D0 + 19) ≠ 0) (hz1 : z < 2 ^ 256) (hD0 : D0 ≤ 76) (hsb : sepb < 256)
    (hb : 0x180 ≤ b) (hb8 : b % 8 = 0) (hb2 : b + 0x198 ≤ 2 ^ 48)
    (hw : M.accessible (b - 0x180) (0x180 + 0x198) true = true)
    (hd : TabsOK M)
    (hx15 : s.xmm 15 = 0) (hdf : s.df = false)
    (e0 : s.regs 0 = BitVec.ofNat 64 19) (e1 : s.regs 1 = BitVec.ofNat 64 (132 - cOf D0)) (e2 : s.regs 2 = BitVec.ofNat 64 (b + 0x40))
    (e6 : s.regs 6 = BitVec.ofNat 64 (cOf D0 % 4)) (e7 : s.regs 7 = BitVec.ofNat 64 (b + 0x130)) (e9 : s.regs 9 = BitVec.ofNat 64 (b + 0x150))
    (e4 : s.regs 4 = BitVec.ofNat 64 b) (e5 : s.regs 5 = BitVec.ofNat 64 (b + 0x178))
    (hg3 : M.readLE ((s.regs 14).toNat + 16) 8 + 0x100 < b) (hg1 : (s.regs 14).toNat + 24 ≤ 2 ^ 48)
    (hg2 : M.accessible ((s.regs 14).toNat + 16) 8 false = true)
    (hgd : (s.regs 14).toNat + 16 + 8 ≤ b - 0x180 ∨ b + 0x198 ≤ (s.regs 14).toNat + 16)
    (hym : Fv256.B.wv M (b + 0x130) 4 = z / 10 ^ D0) (hdm : Fv256.B.wv M (b + 0x150) 4 = 10 ^ 19)
    (hsep : M.readLE (b + 0x190) 1 = sepb) (hout : OutIs M (b + 215) sepb z (cOf D0)) :
    ReachesRet Fv256.PrettyProg.program (BitVec.ofNat 64 pdH) s
      (fun S' => S'.regs 0 = BitVec.ofNat 64 19 ∧ S'.regs 1 = BitVec.ofNat 64 (132 - cOf (D0 + 19)) ∧
        S'.regs 2 = BitVec.ofNat 64 (b + 0x40) ∧ S'.regs 6 = BitVec.ofNat 64 (cOf (D0 + 19) % 4) ∧
        S'.regs 7 = BitVec.ofNat 64 (b + 0x130) ∧ S'.regs 9 = BitVec.ofNat 64 (b + 0x150) ∧
        S'.regs 4 = BitVec.ofNat 64 b ∧ S'.regs 5 = BitVec.ofNat 64 (b + 0x178) ∧ S'.regs 14 = s.regs 14 ∧
        S'.xmm 15 = 0 ∧ S'.df = false ∧
        Fv256.B.wv S'.mem (b + 0x130) 4 = z / 10 ^ (D0 + 19) ∧ Fv256.B.wv S'.mem (b + 0x150) 4 = 10 ^ 19 ∧
        MemFrame M S'.mem [(b - 0x180, b + 376)] ∧ OutIs S'.mem (b + 215) sepb z (cOf (D0 + 19)) ∧ TabsOK S'.mem) := by
  have hrlt : z / 10 ^ D0 % 10 ^ 19 < 10 ^ 19 := Nat.mod_lt _ (by decide)
  have hnd19 : decLen (z / 10 ^ D0 % 10 ^ 19) ≤ 19 := decLen_le_of_lt_pow _ 19 (by decide) hrlt
  have hnd1 := decLen_pos (z / 10 ^ D0 % 10 ^ 19)
  have hlt := decLen_lt_pow (z / 10 ^ D0 % 10 ^ 19)
  refine Fv256.E.reachesRet_bind' (pd_chunk_core s b z D0 sepb M hpc hM hy0 hz1 hD0 hsb hb hb8 hb2 hw hd hx15 hdf e0 e1 e2 e6 e7 e9 e4 e5
    hg3 hg1 hg2 hgd hym hdm hsep hout) ?_
  intro S1 hrip ⟨r0, r1, r3, r4, r5, r11, r12, r13, r14, rx, rdf, ry, rd, rfr, rout, rtab⟩
  generalize hndd : decLen (z / 10 ^ D0 % 10 ^ 19) = nn at hnd19 hnd1 hlt r3 r12 r13 rout
  have hwaS : S1.mem.accessible (b - 0x180) (0x180 + 0x198) true = true := by rw [rfr.accessible]; exact hw
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
  refine Fv256.E.reachesRet_bind' (pd_tail_nz S1 b (z / 10 ^ D0 / 10 ^ 19) hrip r4 hb hb2
    (by rw [rfr.accessible]; exact accessible_sub hw (Or.inr rfl) (by omega) (by omega)) ry hy1) ?_
  intro S2 hrip2 ⟨t2, tk, tm, tx, tdf⟩
  refine ReachesRet.mono (pd_pad_loop b D0 nn sepb z hsb hb hb2 hnd1 hnd19 hcb hpadz (19 - nn) (Nat.le_refl _) S2 hrip2
    (by rw [tm, rfr.accessible]; exact accessible_sub hw (Or.inr rfl) (by omega) (by omega))
    (by rw [t2]; simp) (by rw [tk 3 (by simp)]; exact r3) (by rw [tk 4 (by simp)]; exact r4)
    (by rw [tk 11 (by simp)]; exact r11)
    (by rw [tk 12 (by simp), r12, show D0 + 19 - (19 - nn) = D0 + nn by omega])
    (by rw [tk 13 (by simp), r13, show D0 + 19 - (19 - nn) = D0 + nn by omega])
    (by rw [tm, show D0 + 19 - (19 - nn) = D0 + nn by omega]; exact rout)) ?_
  rintro S ⟨q0, q1, q2, q6, q7, q9, qk, qx, qdf, qfr0, qout⟩
  have qfr : MemFrame S1.mem S.mem [(b + 83, b + 216)] := by rw [← tm]; exact qfr0
  refine ⟨?_, q1, ?_, q6, q7, q9, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, qout, ?_⟩
  · rw [q0, tk 1 (by simp)]; exact r1
  · rw [q2, tk 0 (by simp)]; exact r0
  · rw [qk 4 (by simp), tk 4 (by simp)]; exact r4
  · rw [qk 5 (by simp), tk 5 (by simp)]; exact r5
  · rw [qk 14 (by simp), tk 14 (by simp)]; exact r14
  · rw [qx, tx]; exact rx
  · rw [qdf, tdf]; exact rdf
  · rw [wv_frame qfr _ (by simp only [Outside, and_true]; omega), ry, digits_shift]
  · rw [wv_frame qfr _ (by simp only [Outside, and_true]; omega)]; exact rd
  · exact MemFrame.trans (rs := [(b - 0x180, b + 376)]) (rs' := [(b - 0x180, b + 376)]) rfr (qfr.mono (by
      intro a n h; simp only [Outside, and_true] at h ⊢; omega)) (fun a n h => ⟨h, h⟩)
  · refine rtab.frame qfr ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact accessible_sub hwaS (Or.inr rfl) (by omega) (by omega)

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- The final chunk (`z / 10^(D0+19) = 0`): to `pdF` with all `plen z` cells produced. -/
theorem pd_chunk_final (s : State) (b z D0 sepb : Nat) (M : Memory) (hpc : s.rip = BitVec.ofNat 64 pdH) (hM : s.mem = M)
    (hy0 : z / 10 ^ D0 ≠ 0) (hy' : z / 10 ^ (D0 + 19) = 0) (hz1 : z < 2 ^ 256) (hD0 : D0 ≤ 76) (hsb : sepb < 256)
    (hb : 0x180 ≤ b) (hb8 : b % 8 = 0) (hb2 : b + 0x198 ≤ 2 ^ 48)
    (hw : M.accessible (b - 0x180) (0x180 + 0x198) true = true)
    (hd : TabsOK M)
    (hx15 : s.xmm 15 = 0) (hdf : s.df = false)
    (e0 : s.regs 0 = BitVec.ofNat 64 19) (e1 : s.regs 1 = BitVec.ofNat 64 (132 - cOf D0)) (e2 : s.regs 2 = BitVec.ofNat 64 (b + 0x40))
    (e6 : s.regs 6 = BitVec.ofNat 64 (cOf D0 % 4)) (e7 : s.regs 7 = BitVec.ofNat 64 (b + 0x130)) (e9 : s.regs 9 = BitVec.ofNat 64 (b + 0x150))
    (e4 : s.regs 4 = BitVec.ofNat 64 b) (e5 : s.regs 5 = BitVec.ofNat 64 (b + 0x178))
    (hg3 : M.readLE ((s.regs 14).toNat + 16) 8 + 0x100 < b) (hg1 : (s.regs 14).toNat + 24 ≤ 2 ^ 48)
    (hg2 : M.accessible ((s.regs 14).toNat + 16) 8 false = true)
    (hgd : (s.regs 14).toNat + 16 + 8 ≤ b - 0x180 ∨ b + 0x198 ≤ (s.regs 14).toNat + 16)
    (hym : Fv256.B.wv M (b + 0x130) 4 = z / 10 ^ D0) (hdm : Fv256.B.wv M (b + 0x150) 4 = 10 ^ 19)
    (hsep : M.readLE (b + 0x190) 1 = sepb) (hout : OutIs M (b + 215) sepb z (cOf D0)) :
    ReachesRet Fv256.PrettyProg.program (BitVec.ofNat 64 pdF) s
      (fun S' => S'.regs 12 = BitVec.ofNat 64 (132 - plen z) ∧
        S'.regs 4 = BitVec.ofNat 64 b ∧ S'.regs 5 = BitVec.ofNat 64 (b + 0x178) ∧ S'.regs 14 = s.regs 14 ∧
        S'.xmm 15 = 0 ∧ S'.df = false ∧
        MemFrame M S'.mem [(b - 0x180, b + 376)] ∧ OutIs S'.mem (b + 215) sepb z (plen z) ∧ TabsOK S'.mem) := by
  have hrlt : z / 10 ^ D0 % 10 ^ 19 < 10 ^ 19 := Nat.mod_lt _ (by decide)
  have hy10 : z / 10 ^ D0 < 10 ^ 19 := by
    have := Nat.div_eq_zero_iff.mp (show z / 10 ^ D0 / 10 ^ 19 = 0 by rw [digits_shift]; exact hy')
    omega
  have h10 : 10 ^ D0 ≤ z := Nat.le_of_not_lt (fun hc => hy0 (Nat.div_eq_of_lt hc))
  have hdz : decLen z = decLen (z / 10 ^ D0) + D0 := decLen_div_pow z D0 h10
  have hnd : decLen (z / 10 ^ D0 % 10 ^ 19) = decLen (z / 10 ^ D0) := by rw [Nat.mod_eq_of_lt hy10]
  refine Fv256.E.reachesRet_bind' (pd_chunk_core s b z D0 sepb M hpc hM hy0 hz1 hD0 hsb hb hb8 hb2 hw hd hx15 hdf e0 e1 e2 e6 e7 e9 e4 e5
    hg3 hg1 hg2 hgd hym hdm hsep hout) ?_
  intro S1 hrip ⟨r0, r1, r3, r4, r5, r11, r12, r13, r14, rx, rdf, ry, rd, rfr, rout, rtab⟩
  have hD : D0 + decLen (z / 10 ^ D0 % 10 ^ 19) = decLen z := by rw [hnd]; omega
  rw [hD, cOf_plen] at r12 rout
  have hwaS : S1.mem.accessible (b - 0x180) (0x180 + 0x198) true = true := by rw [rfr.accessible]; exact hw
  have hy2 : z / 10 ^ D0 / 10 ^ 19 = 0 := by rw [digits_shift]; exact hy'
  refine ReachesRet.mono (pd_tail_z S1 b hrip r4 hb hb2
    (by rw [rfr.accessible]; exact accessible_sub hw (Or.inr rfl) (by omega) (by omega)) (by rw [ry, hy2])) ?_
  rintro S ⟨tk, tm, tx, tdf⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tk 12 (by simp)]; exact r12
  · rw [tk 4 (by simp)]; exact r4
  · rw [tk 5 (by simp)]; exact r5
  · rw [tk 14 (by simp)]; exact r14
  · rw [tx]; exact rx
  · rw [tdf]; exact rdf
  · rw [tm]; exact rfr
  · rw [tm]; exact rout
  · rw [tm]; exact rtab
end Fv256.Amd64.Pd
