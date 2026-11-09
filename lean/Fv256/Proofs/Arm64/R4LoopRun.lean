import Fv256.Proofs.Arm64.R4G.G_2f4_310
import Fv256.Proofs.Arm64.R4G.G_310_2f4
import Fv256.Proofs.Arm64.R4G.G_310_314
import Fv256.Proofs.Arm64.R4Exit
import Fv256.Proofs.Arm64.R4Loop

/-! `reduce4` (arm64): the final `for r >= m { r -= m }` loop (`b9864 .. b9880`), by induction on a bound for `r / m`. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.ReduceSpec Fv256.Arm64.R4Nat

namespace Fv256.Arm64.R4Seg

theorem lt64 {S : State} {k x : Nat} (h : (S.regs k).toNat = x) : x < 2 ^ 64 := by rw [← h]; exact BitVec.isLt _

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem loop_run (s : State) (hs : R4Pre s) :
    ∀ (n : Nat) (S : State) (m1 m0 c1 c2 c4 c3 c0 m3 m2 : Nat),
      S.pc = BitVec.ofNat 64 (r4Entry + 0x2f4) → R4Regs s S → R4Mem s S.mem →
      L2f4 S m1 m0 c1 c2 c4 c3 c0 m3 0 m2 →
      c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 + 2 ^ 256 * c4 <
        n * (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3) + (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3) →
      ReachesRet Fv256.Arm64.ReduceProg.program (s.regs 30) S
        (fun S' => R4PostV s S' ((c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 + 2 ^ 256 * c4) %
          (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3))) := by
  intro n
  induction n with
  | zero =>
    intro S m1 m0 c1 c2 c4 c3 c0 m3 m2 hpc hR hM hL hlt
    have hL' := hL
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e12⟩ := hL'
    have bm1 := lt64 e1
    have bm0 := lt64 e2
    have bc1 := lt64 e3
    have bc2 := lt64 e4
    have bc4 := lt64 e5
    have bc3 := lt64 e6
    have bc0 := lt64 e7
    have bm3 := lt64 e8
    have bm2 := lt64 e12
    refine Fv256.Arm64.SegCompose.seg_trans (g_2f4_310 s S hpc hs hR hM m1 m0 c1 c2 c4 c3 c0 m3 0 m2 hL) ?_
    intro S1 hpc1 hq1
    unfold P_2f4_310 at hq1
    obtain ⟨r5, r10, r11, r13, r14, r15, hL1, h5, h10, h11, h13, h14, h15, hR1, hM1⟩ := hq1
    have hk := loop_sub c0 c1 c2 c3 c4 m0 m1 m2 m3 r10 r11 r13 r14 r5 r15 bc0 bc1 bc2 bc3 bc4 bm0 bm1 bm2 bm3 h10 h11 h13 h14 h5 h15
    by_cases hc : r15 = 0
    · exfalso; exact zero_false _ _ hlt (hk.1.1 hc)
    · have hlt2 : c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 + 2 ^ 256 * c4 < m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3 :=
        Nat.lt_of_not_ge (fun hh => hc (hk.1.2 hh))
      obtain ⟨hc4, hmod⟩ := exit_nat c0 c1 c2 c3 c4 _ bc0 bc1 bc2 bc3 (bound_N m0 m1 m2 m3 bm0 bm1 bm2 bm3) hlt2
      subst hc4
      refine Fv256.Arm64.SegCompose.seg_trans (g_310_314 s S1 hpc1 hs hR1 hM1 m1 m0 c1 c2 r5 c3 c0 m3 0 r10 r11 m2 r13 r14 r15 hL1 hc) ?_
      intro S2 hpc2 hq2
      unfold P_310_314 at hq2
      obtain ⟨hL2, hR2, hM2⟩ := hq2
      refine Fv256.Arm64.SegCompose.seg_mono (r4_exit s S2 hpc2 hs hR2 hM2 c1 c2 c3 c0 hL2) ?_
      intro S' h
      unfold R4PostV at h ⊢
      have e1 : c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 + 2 ^ 256 * 0 = c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 := Nat.add_zero _
      rw [e1, hmod]
      exact h
  | succ n ih =>
    intro S m1 m0 c1 c2 c4 c3 c0 m3 m2 hpc hR hM hL hlt
    have hL' := hL
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e12⟩ := hL'
    have bm1 := lt64 e1
    have bm0 := lt64 e2
    have bc1 := lt64 e3
    have bc2 := lt64 e4
    have bc4 := lt64 e5
    have bc3 := lt64 e6
    have bc0 := lt64 e7
    have bm3 := lt64 e8
    have bm2 := lt64 e12
    refine Fv256.Arm64.SegCompose.seg_trans (g_2f4_310 s S hpc hs hR hM m1 m0 c1 c2 c4 c3 c0 m3 0 m2 hL) ?_
    intro S1 hpc1 hq1
    unfold P_2f4_310 at hq1
    obtain ⟨r5, r10, r11, r13, r14, r15, hL1, h5, h10, h11, h13, h14, h15, hR1, hM1⟩ := hq1
    have hk := loop_sub c0 c1 c2 c3 c4 m0 m1 m2 m3 r10 r11 r13 r14 r5 r15 bc0 bc1 bc2 bc3 bc4 bm0 bm1 bm2 bm3 h10 h11 h13 h14 h5 h15
    by_cases hc : r15 = 0
    · have hsub := hk.2 hc
      have hge := hk.1.1 hc
      refine Fv256.Arm64.SegCompose.seg_trans (g_310_2f4 s S1 hpc1 hs hR1 hM1 m1 m0 c1 c2 r5 c3 c0 m3 0 r10 r11 m2 r13 r14 r15 hL1 hc) ?_
      intro S2 hpc2 hq2
      unfold P_310_2f4 at hq2
      obtain ⟨hL2, hR2, hM2⟩ := hq2
      refine Fv256.Arm64.SegCompose.seg_mono (ih S2 m1 m0 r11 r13 r5 r14 r10 m3 m2 hpc2 hR2 hM2 hL2 (back_lt _ _ n _ hlt hsub)) ?_
      intro S' h
      have e : (c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 + 2 ^ 256 * c4) % (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3) =
          (r10 + 2 ^ 64 * r11 + 2 ^ 128 * r13 + 2 ^ 192 * r14 + 2 ^ 256 * r5) % (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3) := by
        rw [← hsub, Nat.add_mod_right]
      unfold R4PostV at h ⊢
      rw [e]
      exact h
    · have hlt2 : c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 + 2 ^ 256 * c4 < m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3 :=
        Nat.lt_of_not_ge (fun hh => hc (hk.1.2 hh))
      obtain ⟨hc4, hmod⟩ := exit_nat c0 c1 c2 c3 c4 _ bc0 bc1 bc2 bc3 (bound_N m0 m1 m2 m3 bm0 bm1 bm2 bm3) hlt2
      subst hc4
      refine Fv256.Arm64.SegCompose.seg_trans (g_310_314 s S1 hpc1 hs hR1 hM1 m1 m0 c1 c2 r5 c3 c0 m3 0 r10 r11 m2 r13 r14 r15 hL1 hc) ?_
      intro S2 hpc2 hq2
      unfold P_310_314 at hq2
      obtain ⟨hL2, hR2, hM2⟩ := hq2
      refine Fv256.Arm64.SegCompose.seg_mono (r4_exit s S2 hpc2 hs hR2 hM2 c1 c2 c3 c0 hL2) ?_
      intro S' h
      unfold R4PostV at h ⊢
      have e1 : c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 + 2 ^ 256 * 0 = c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 := Nat.add_zero _
      rw [e1, hmod]
      exact h

end Fv256.Arm64.R4Seg
