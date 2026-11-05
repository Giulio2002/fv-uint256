import Fv256.ChainProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.DivWork

abbrev by1 : Nat := segAddr Fv256.ChainProg.program "github.com/holiman/uint256.udivremBy1"
abbrev by1Head : Nat := by1 + 0x64

theorem by1Head_lt : by1Head + 200 < 2 ^ 47 := by decide

set_option maxHeartbeats 8000000 in
theorem by1_loop (s0 : State) (q u n d v : Nat) (hn : 2 ≤ n) (hn2 : n < 2 ^ 20)
    (hd1 : 2 ^ 63 ≤ d) (hd2 : d < 2 ^ 64) (hv : v + 2 ^ 64 = (2 ^ 64 * 2 ^ 64 - 1) / d)
    (hq : (s0.regs 0).toNat = q) (hu : (s0.regs 7).toNat = u) (hqlen : n - 1 ≤ (s0.regs 3).toNat)
    (hd : (s0.regs 9).toNat = d)
    (hqa : s0.mem.accessible q (8 * (n - 1)) true = true) (hqb : q + 8 * (n - 1) ≤ 2 ^ 48)
    (hua : s0.mem.accessible u (8 * n) false = true) (hub : u + 8 * n ≤ 2 ^ 48)
    (hqu : q + 8 * (n - 1) ≤ u ∨ u + 8 * n ≤ q)
    (hqs : q + 8 * (n - 1) ≤ (s0.regs 4).toNat - 8 ∨ (s0.regs 4).toNat + 40 ≤ q)
    (hus : u + 8 * n ≤ (s0.regs 4).toNat - 8 ∨ (s0.regs 4).toNat + 40 ≤ u)
    (hsp : 8 ≤ (s0.regs 4).toNat) (hspb : (s0.regs 4).toNat + 40 ≤ 2 ^ 48)
    (hspa : s0.mem.accessible ((s0.regs 4).toNat - 8) 48 true = true)
    (hretlt : s0.mem.readLE (s0.regs 4).toNat 8 < 2 ^ 47) :
    ∀ k (rem : Nat) (R : Nat → W64) (fl : Flags) (M : Memory), k ≤ n - 1 → rem < d →
      R 0 = BitVec.ofNat 64 v → R 1 = BitVec.ofNat 64 rem → R 2 = BitVec.ofNat 64 k - 1 →
      R 4 = s0.regs 4 - 8 → R 5 = s0.regs 4 - 8 → R 8 = BitVec.ofNat 64 q →
      (∀ i, i ∉ [0, 1, 2, 4, 5, 6, 8, 10, 11, 12] → R i = s0.regs i) →
      Fv256.B.wv s0.mem (u + 8 * k) (n - k) = d * Fv256.B.wv M (q + 8 * k) (n - 1 - k) + rem →
      (∀ i, i < n → M.readLE (u + 8 * i) 8 = s0.mem.readLE (u + 8 * i) 8) →
      MemFrame s0.mem M [(q, q + 8 * (n - 1)), ((s0.regs 4).toNat - 8, (s0.regs 4).toNat),
        ((s0.regs 4).toNat + 8, (s0.regs 4).toNat + 16), ((s0.regs 4).toNat + 32, (s0.regs 4).toNat + 40)] →
      M.readLE ((s0.regs 4).toNat - 8) 8 = (s0.regs 5).toNat →
      ReachesRet Fv256.ChainProg.program (retAddrOf s0)
        { s0 with regs := R, rip := BitVec.ofNat 64 by1Head, flags := fl, mem := M }
        (fun S' => ∃ (rem' : Nat) (R' : Nat → W64) (fl' : Flags) (M' : Memory),
          S' = { s0 with regs := R', rip := retAddrOf s0, flags := fl', mem := M' } ∧
          R' 0 = BitVec.ofNat 64 rem' ∧ R' 4 = s0.regs 4 + 8 ∧ R' 8 = BitVec.ofNat 64 q ∧
          (∀ i, i ∉ [0, 1, 2, 4, 6, 8, 10, 11, 12] → R' i = s0.regs i) ∧
          rem' < d ∧ Fv256.B.wv s0.mem u n = d * Fv256.B.wv M' q (n - 1) + rem' ∧
          MemFrame s0.mem M' [(q, q + 8 * (n - 1)), ((s0.regs 4).toNat - 8, (s0.regs 4).toNat),
            ((s0.regs 4).toNat + 8, (s0.regs 4).toNat + 16), ((s0.regs 4).toNat + 32, (s0.regs 4).toNat + 40)]) := by
  intro k
  induction k with
  | zero =>
    intro rem R fl M hk hrem h0 h1 h2 h4 h5 h8 hRu hI hu' hfr hrbp
    have hcode := by1Head_lt
    have hMa : M.accessible ((s0.regs 4).toNat - 8) 48 true = true := by rw [hfr.accessible]; exact hspa
    have hMq : M.accessible q (8 * (n - 1)) true = true := by rw [hfr.accessible]; exact hqa
    have hMu : M.accessible u (8 * n) false = true := by rw [hfr.accessible]; exact hua
    have hmsb : (18446744073709551615#64).msb = true := by decide
    janus64_run [hmsb, h0, h1, h2, h4, h5, h8]
    refine ⟨rem, _, _, M, rfl, ?_, ?_, ?_, ?_, hrem, ?_, hfr⟩
    · simp [setRegF]
    · simp [setRegF]
    · simp [setRegF, h8]
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      simp only [setRegF]
      by_cases h5' : i = 5
      · subst h5'; simp
      · rw [if_neg h5', if_neg (by omega : ¬ i = 4), if_neg (by omega : ¬ i = 0)]
        exact hRu i (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)
    · simpa using hI
  | succ k ih =>
    intro rem R fl M hk hrem h0 h1 h2 h4 h5 h8 hRu hI hu' hfr hrbp
    have hcode := by1Head_lt
    have hMa : M.accessible ((s0.regs 4).toNat - 8) 48 true = true := by rw [hfr.accessible]; exact hspa
    have hMq : M.accessible q (8 * (n - 1)) true = true := by rw [hfr.accessible]; exact hqa
    have hMu : M.accessible u (8 * n) false = true := by rw [hfr.accessible]; exact hua
    have hj : BitVec.ofNat 64 (k + 1) - (1 : BitVec 64) = BitVec.ofNat 64 k := by bv_omega
    have hjt : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat]; omega
    rw [hj] at h2
    have h3 : R 3 = s0.regs 3 := hRu 3 (by simp)
    have h7 : R 7 = s0.regs 7 := hRu 7 (by simp)
    have h9 : R 9 = s0.regs 9 := hRu 9 (by simp)
    have h14 : R 14 = s0.regs 14 := hRu 14 (by simp)
    have hmsbk : (BitVec.ofNat 64 k).msb = false := by
      rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat]; simp; omega
    janus64_run [hjt, hu, hd, h0, h1, h2, h3, h4, h5, h7, h8, h9, h14, hmsbk] until [by1Head]
    obtain ⟨uk, huk⟩ : ∃ uk, uk = s0.mem.readLE (u + k * 8) 8 := ⟨_, rfl⟩
    have hukB : uk < 2 ^ 64 := by rw [huk]; have := Janus.Arm64.Memory.readLE_lt s0.mem (u + k * 8) 8; simpa using this
    have hvB : v < 2 ^ 64 := Fv256.B.recip_lt d v hd1 hv
    have hvm : v % 18446744073709551616 = v := Nat.mod_eq_of_lt hvB
    have hd9 : (s0.regs 9).toNat = d := hd
    have hcorr := Fv256.B.div2by1_correct (2 ^ 64) d (v + 2 ^ 64) rem uk (by omega) hd2 (by rw [← hv]) (by omega) hukB
    have hsub : v + 2 ^ 64 - 2 ^ 64 = v := by omega
    rw [hsub] at hcorr
    refine Fv256.B.reachesRet_mem_congr _ (M.writeLE (q + 8 * k) 8 (Fv256.B.div2by1 (2 ^ 64) d v rem uk).1) ?main ?memeq
    case memeq =>
      rw [show q + k * 8 = q + 8 * k by omega]
      apply Fv256.B.writeLE_val_congr
      simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, Nat.reducePow, apply_ite BitVec.toNat, hvm, hd9, ← huk]
      div2_close v rem uk d hvB hukB hd1 hd2 hrem
    case main =>
      refine ih (Fv256.B.div2by1 (2 ^ 64) d v rem uk).2 _ _ _ (by omega) ?hrem' ?r0 ?r1 ?r2 ?r4 ?r5 ?r8 ?ru ?hI ?hu ?hfr ?hrbp
      case hrem' => rw [hcorr]; exact Nat.mod_lt _ (by omega)
      case r0 => simp [setRegF]
      case r1 =>
        simp (config := { decide := true }) only [setRegF, ↓reduceIte]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, Nat.reducePow, apply_ite BitVec.toNat, hvm, hd9, ← huk]
        div2_close v rem uk d hvB hukB hd1 hd2 hrem
      case r2 => simp [setRegF]
      case r4 => simp [setRegF, h4]
      case r5 => simp [setRegF, h5]
      case r8 => simp [setRegF, h8]
      case ru =>
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
        simp only [setRegF]
        repeat' rw [if_neg (by omega)]
        exact hRu i (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)
      case hI =>
        have hQlt : (rem * 2 ^ 64 + uk) / d < 2 ^ 64 := by
          apply Nat.div_lt_of_lt_mul
          have : (rem + 1) * 2 ^ 64 ≤ d * 2 ^ 64 := Nat.mul_le_mul_right _ hrem
          rw [Nat.add_mul] at this
          rw [Nat.mul_comm d]; omega
        have hT := Nat.div_add_mod (rem * 2 ^ 64 + uk) d
        have e1 : n - k = (n - (k + 1)) + 1 := by omega
        have e2 : n - 1 - k = (n - 1 - (k + 1)) + 1 := by omega
        have ea : u + 8 * (k + 1) = u + 8 * k + 8 := by omega
        have eb : q + 8 * (k + 1) = q + 8 * k + 8 := by omega
        rw [ea, eb] at hI
        rw [e1, e2, Fv256.B.wv_succ, Fv256.B.wv_succ, Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (Or.inl (by omega)),
          Janus.Arm64.Memory.readLE_writeLE_self]
        rw [show u + 8 * k = u + k * 8 by omega, ← huk, hcorr]
        simp only [Nat.reducePow, Nat.mod_eq_of_lt hQlt]
        generalize Fv256.B.wv M (q + 8 * k + 8) (n - 1 - (k + 1)) = W at *
        grind
      case hu =>
        intro i hi
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
        exact hu' i hi
      case hfr => exact hfr.writeLE _ (List.mem_cons_self ..) (by omega) (by omega)
      case hrbp =>
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
        exact hrbp

end Fv256.Amd64.DivWork
