import Fv256.Arm64.DecProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.DecMath
import Fv256.Arm64.DecT
import Fv256.Arm64.DecA
import Fv256.Arm64.DecE
import Fv256.Arm64.DecG
import Fv256.Arm64.DecH
import Fv256.Arm64.DecI
import Fv256.Arm64.DecJ

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI
open Fv256.E

namespace Fv256.Arm64.Dec

theorem dig_shift (u0 c k : Nat) : u0 / 10 ^ c / 10 ^ k % 10 = u0 / 10 ^ (c + k) % 10 := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

/-- The registers `formatBase10` may change. -/
def Clob : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 16, 29, 30]

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem outer (ptr len u0 i0 bp ret : Nat) (hu0 : u0 < 2 ^ 64) (hdl : decLen u0 ≤ i0) (hil : i0 ≤ len)
    (hp : ptr + len ≤ 2 ^ 48) (hret : ret < 2 ^ 48) (hret4 : ret % 4 = 0) :
    ∀ u c (s : State), u = u0 / 10 ^ c → c + decLen u ≤ i0 →
      s.mem.accessible ptr len true = true → TabsOK s.mem → s.pc = BitVec.ofNat 64 (fb + 0x28) →
      s.regs 0 = BitVec.ofNat 64 ptr → s.regs 2 = BitVec.ofNat 64 len → s.regs 1 = BitVec.ofNat 64 (i0 - c) →
      s.regs 3 = BitVec.ofNat 64 u → s.regs 30 = BitVec.ofNat 64 ret →
      s.sp.toNat % 16 = 0 → 8 ≤ s.sp.toNat → s.sp.toNat + 16 < 2 ^ 48 →
      s.mem.accessible (s.sp.toNat - 8) 16 false = true → (ptr + len ≤ s.sp.toNat - 8 ∨ s.sp.toNat + 16 ≤ ptr) →
      s.mem.readLE (s.sp.toNat - 8) 8 = bp → s.mem.readLE s.sp.toNat 8 = ret →
      (∀ k, k < c → s.mem.readLE (ptr + i0 - 1 - k) 1 = 48 + u0 / 10 ^ k % 10) → (0 < u ∨ c = 0) →
      ReachesRet Fv256.Arm64.DecProg.program (BitVec.ofNat 64 ret) s (fun S' =>
        S'.regs 0 = BitVec.ofNat 64 (i0 - decLen u0) ∧ S'.sp = s.sp + 16#64 ∧ S'.regs 29 = BitVec.ofNat 64 bp ∧
        (∀ k, k ∉ Clob → S'.regs k = s.regs k) ∧
        (∀ k, k < decLen u0 → S'.mem.readLE (ptr + i0 - 1 - k) 1 = 48 + u0 / 10 ^ k % 10) ∧
        MemFrame s.mem S'.mem [(ptr + i0 - decLen u0, ptr + i0 - c)] ∧ TabsOK S'.mem) := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
    intro c s hu hdc hacc hd hpc e0 e2 e1 e3 hl hal h8 hsp2 hsa hout m0 m1 hw hpos
    have hu64 : u < 2 ^ 64 := by rw [hu]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hu0
    have hc0 : decLen u0 = decLen u + c := by
      by_cases hc : c = 0
      · subst hc; simp [hu]
      · have : 0 < u := by omega
        have h1 : 10 ^ c ≤ u0 := by
          rw [hu] at this
          exact (Nat.le_div_iff_mul_le (Nat.one_le_pow c 10 (by omega))).1 this |> fun h => by omega
        rw [decLen_div_pow u0 c h1, ← hu]
    by_cases hbig : 2 ^ 29 ≤ u
    · by_cases h9 : 10 ^ 9 ≤ u
      · have hdl9 : decLen u = decLen (u / 10 ^ 9) + 9 := decLen_div_pow u 9 h9
        refine reachesRet64_bind (chunk s (fb + 0x28) ptr len u (i0 - c) (Or.inl ⟨h9, rfl⟩) hu64 hbig (by omega) (by omega) hp hacc hd
          hpc e0 e2 e1 e3) ?_
        rintro S hpc1 ⟨a0, a2, a1, a4, a3, ak, asp, am, afr, atab⟩
        have hacc1 : S.mem.accessible ptr len true = true := by rw [afr.accessible]; exact hacc
        have hw1 : ∀ k, k < c + 9 → S.mem.readLE (ptr + i0 - 1 - k) 1 = 48 + u0 / 10 ^ k % 10 := by
          intro k hk
          by_cases hkc : k < c
          · have hout' : Outside (ptr + i0 - 1 - k) 1 [(ptr + (i0 - c) - 9, ptr + (i0 - c))] := by
              simp only [Outside, and_true]; omega
            rw [afr.readLE _ _ hout', hw k hkc]
          · have := am (k - c) (by omega)
            rw [show ptr + (i0 - c) - 1 - (k - c) = ptr + i0 - 1 - k by omega] at this
            rw [this, hu, dig_shift, show c + (k - c) = k by omega]
        have hu' : u / 10 ^ 9 = u0 / 10 ^ (c + 9) := by
          rw [hu, Nat.div_div_eq_div_mul, ← Nat.pow_add]
        have hne : u / 10 ^ 9 ≠ 0 := by omega
        obtain ⟨sm0, sm1, sacc⟩ := stack_pres64 afr (by omega) (by omega) hout h8
        refine reachesRet64_mono (ih (u / 10 ^ 9) (Nat.div_lt_self (by omega) (by decide)) (c + 9) S hu' (by omega) hacc1 atab hpc1
          a0 a2 (by rw [a1]; congr 1) (a3 hne) (by rw [ak 30 (by simp [Clob]), hl])
          (by rw [asp]; exact hal) (by rw [asp]; exact h8) (by rw [asp]; exact hsp2)
          (by rw [asp, sacc]; exact hsa) (by rw [asp]; exact hout) (by rw [asp, sm0, m0]) (by rw [asp, sm1, m1]) hw1
          (Or.inl (by omega))) ?_
        rintro S2 ⟨b0, bsp, b29, bk, bm, bfr, btab⟩
        refine ⟨b0, by rw [bsp, asp], b29, ?_, ?_, ?_, btab⟩
        · intro k hk
          rw [bk k hk, ak k (by simp only [Clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega)]
        · exact bm
        · refine afr.trans bfr (rs'' := [(ptr + i0 - decLen u0, ptr + i0 - c)]) ?_
          intro a n h
          simp only [Outside, and_true] at h ⊢
          omega
      · have hu9 : u < 10 ^ 9 := by omega
        have hdl9 : decLen u = 9 := decLen_of u 9 (by omega) (by
          have : 10 ^ (9 - 1) ≤ 2 ^ 29 := by decide
          omega) (by omega)
        refine reachesRet64_bind (chunk s (fb + 0x1ec) ptr len u (i0 - c) (Or.inr ⟨hu9, rfl⟩) hu64 hbig (by omega) (by omega) hp hacc hd
          hpc e0 e2 e1 e3) ?_
        rintro S hpc1 ⟨a0, a2, a1, a4, a3, ak, asp, am, afr, atab⟩
        obtain ⟨sm0, sm1, sacc⟩ := stack_pres64 afr (by omega) (by omega) hout h8
        refine reachesRet64_mono (tail_ret S (fb + 0x1ec) bp ret (Or.inr rfl) hpc1 (by rw [asp]; exact hal) (by rw [asp]; exact h8)
          (by rw [asp]; exact hsp2) (by rw [asp, sacc]; exact hsa) (by rw [asp, sm0, m0]) (by rw [asp, sm1, m1])
          (by rw [ak 30 (by simp), hl]) hret hret4) ?_
        rintro S2 ⟨t0, tsp, t29, tk, tm⟩
        refine ⟨?_, by rw [tsp, asp], t29, ?_, ?_, ?_, ?_⟩
        · rw [t0, a1, hc0, hdl9]; congr 1; omega
        · intro k hk
          rw [tk k (by simp only [Clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega),
            ak k (by simp only [Clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega)]
        · intro k hk
          rw [tm]
          rw [hc0, hdl9] at hk
          by_cases hkc : k < c
          · have hout' : Outside (ptr + i0 - 1 - k) 1 [(ptr + (i0 - c) - 9, ptr + (i0 - c))] := by
              simp only [Outside, and_true]; omega
            rw [afr.readLE _ _ hout', hw k hkc]
          · have := am (k - c) (by omega)
            rw [show ptr + (i0 - c) - 1 - (k - c) = ptr + i0 - 1 - k by omega] at this
            rw [this, hu, dig_shift, show c + (k - c) = k by omega]
        · rw [tm, hc0, hdl9]
          exact afr.mono (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)
        · rw [tm]; exact atab
    · have hu29 : u < 2 ^ 29 := by omega
      have hdu : decLen u ≤ i0 - c := by omega
      refine reachesRet64_bind (to_final s u hu29 hpc e3) ?_
      rintro S hpc1 ⟨a3, ak, asp, amem⟩
      have hacc1 : S.mem.accessible ptr len true = true := by rw [amem]; exact hacc
      have hd1 : TabsOK S.mem := by rw [amem]; exact hd
      refine reachesRet64_bind (fin_loop ptr len u (i0 - c) hu29 hdu (by omega) hp u 0 S (by simp) (by simpa using hdu)
        hacc1 hd1 hpc1 (by rw [ak 0 (by simp), e0]) (by rw [ak 2 (by simp), e2]) (by rw [ak 1 (by simp), e1]; rfl) a3
        (by intro k hk; omega)) ?_
      rintro S2 hpc2 ⟨c', hc1, hz, hdc', hlt100, b0, b2, b1, b3, bk, bsp, bm, bfr, btab⟩
      have hacc2 : S2.mem.accessible ptr len true = true := by rw [bfr.accessible]; exact hacc1
      have hc'0 : decLen u = c' + decLen (u / 10 ^ c') := by
        rcases hz with h | h
        · rw [h]; simp
        · have h1 : 10 ^ c' ≤ u := (Nat.le_div_iff_mul_le (Nat.one_le_pow c' 10 (by omega))).1 h |> fun h => by omega
          have := decLen_div_pow u c' h1
          omega
      have hS2 : TabsOK S2.mem := btab
      refine reachesRet64_bind (fin_last S2 ptr len (u / 10 ^ c') (i0 - c - c') hlt100 (by omega) (by omega) hp hacc2 hS2 hpc2
        b0 b2 (by rw [b1]) b3) ?_
      rintro S3 hpc3 ⟨d0, d2, d1, dk, dsp, dm, dfr, dtab⟩
      have hfrT : MemFrame s.mem S3.mem [(ptr + i0 - c - decLen u, ptr + i0 - c)] := by
        rw [← amem] at *
        refine MemFrame.trans (m' := S2.mem) (rs := [(ptr + i0 - c - decLen u, ptr + i0 - c)])
          (rs' := [(ptr + i0 - c - decLen u, ptr + i0 - c)]) ?_ ?_ (fun a n h => ⟨h, h⟩)
        · exact bfr.mono (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)
        · exact dfr.mono (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)
      obtain ⟨sm0, sm1, sacc⟩ := stack_pres64 hfrT (by omega) (by omega) hout h8
      refine reachesRet64_mono (tail_ret S3 (fb + 0x1cc) bp ret (Or.inl rfl) hpc3 (by rw [dsp, bsp, asp]; exact hal)
        (by rw [dsp, bsp, asp]; exact h8) (by rw [dsp, bsp, asp]; exact hsp2) (by rw [dsp, bsp, asp, sacc]; exact hsa)
        (by rw [dsp, bsp, asp, sm0, m0]) (by rw [dsp, bsp, asp, sm1, m1])
        (by rw [dk 30 (by simp), bk 30 (by simp), ak 30 (by simp), hl]) hret hret4) ?_
      rintro S4 ⟨t0, tsp, t29, tk, tm⟩
      refine ⟨?_, by rw [tsp, dsp, bsp, asp], t29, ?_, ?_, ?_, ?_⟩
      · rw [t0, d1, hc0, hc'0]; congr 1; omega
      · intro k hk
        rw [tk k (by simp only [Clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega),
          dk k (by simp only [Clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega),
          bk k (by simp only [Clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega),
          ak k (by simp only [Clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega)]
      · intro k hk
        rw [tm]
        rw [hc0, hc'0] at hk
        by_cases hkc : k < c
        · have hout1 : Outside (ptr + i0 - 1 - k) 1 [(ptr + (i0 - c - c') - decLen (u / 10 ^ c'), ptr + (i0 - c - c'))] := by
            simp only [Outside, and_true]; omega
          have hout2 : Outside (ptr + i0 - 1 - k) 1 [(ptr + (i0 - c) - c', ptr + (i0 - c) - 0)] := by
            simp only [Outside, and_true]; omega
          rw [dfr.readLE _ _ hout1, bfr.readLE _ _ hout2, amem, hw k hkc]
        · by_cases hk2 : k - c < c'
          · have hout1 : Outside (ptr + i0 - 1 - k) 1 [(ptr + (i0 - c - c') - decLen (u / 10 ^ c'), ptr + (i0 - c - c'))] := by
              simp only [Outside, and_true]; omega
            have := bm (k - c) hk2
            rw [show ptr + (i0 - c) - 1 - (k - c) = ptr + i0 - 1 - k by omega] at this
            rw [dfr.readLE _ _ hout1, this, hu, dig_shift, show c + (k - c) = k by omega]
          · have := dm (k - c - c') (by omega)
            rw [show ptr + (i0 - c - c') - 1 - (k - c - c') = ptr + i0 - 1 - k by omega, hu, dig_shift, dig_shift,
              show c + (c' + (k - c - c')) = k by omega] at this
            rw [this]
      · rw [tm, hc0, hc'0]
        refine hfrT.mono (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)
      · rw [tm]; exact dtab
end Fv256.Arm64.Dec
