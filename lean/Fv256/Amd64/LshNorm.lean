import Fv256.Spec
import Fv256.Util
import Fv256.LshProg
import Fv256.Amd64.LshSum

/-!
# `Lsh` with a normalising shift count (Extracted-free library summary)

`Lsh(z, x, n)` with `n = clz64(x[3])`, `x[3] ≠ 0` (the call in `Reciprocal`): the result's top word has its top bit set.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.LshNorm

open Janus.Arm64 in
theorem clz_norm : ∀ (n x : Nat), x < 2 ^ n → x ≠ 0 →
    2 ^ (n - 1) ≤ x * 2 ^ (clzNat n x) ∧ x * 2 ^ (clzNat n x) < 2 ^ n := by
  intro n
  induction n with
  | zero => intro x hx h0; omega
  | succ n ih =>
    intro x hx h0
    have hc : clzNat (n + 1) x = if x.testBit n = true then 0 else 1 + clzNat n x := rfl
    rw [hc]
    by_cases hb : x.testBit n = true
    · rw [if_pos hb, Nat.pow_zero, Nat.mul_one]
      have h2 : 2 ^ n ≤ x := by
        rcases Nat.lt_or_ge x (2 ^ n) with hlt | hge
        · have := Nat.testBit_lt_two_pow hlt (i := n)
          rw [this] at hb
          exact absurd hb (by decide)
        · exact hge
      rw [Nat.add_sub_cancel]
      omega
    · rw [if_neg hb]
      have hxn : x < 2 ^ n := by
        rcases Nat.lt_or_ge x (2 ^ n) with hlt | hge
        · exact hlt
        · exfalso
          have h1 : x / 2 ^ n = 1 := by
            apply Nat.div_eq_of_lt_le
            · omega
            · have : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
              omega
          apply hb
          rw [Nat.testBit_eq_decide_div_mod_eq, h1]
          decide
      obtain ⟨h1, h2⟩ := ih x hxn h0
      have e : 2 ^ (1 + clzNat n x) = 2 * 2 ^ clzNat n x := by
        rw [Nat.add_comm, Nat.pow_succ]; omega
      rw [e]
      have e2 : x * (2 * 2 ^ clzNat n x) = 2 * (x * 2 ^ clzNat n x) := by
        rw [Nat.mul_left_comm]
      rw [e2]
      cases n with
      | zero => omega
      | succ k =>
        rw [Nat.add_sub_cancel]
        rw [Nat.add_sub_cancel] at h1
        have h3 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
        have h4 : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
        omega


theorem clz_le (x : Nat) (hx : x < 2 ^ 64) (h0 : x ≠ 0) : Janus.Arm64.clzNat 64 x ≤ 63 := by
  obtain ⟨_, h2⟩ := clz_norm 64 x hx h0
  by_cases hh : Janus.Arm64.clzNat 64 x ≤ 63
  · exact hh
  · exfalso
    have : 2 ^ 64 ≤ 2 ^ (Janus.Arm64.clzNat 64 x) := Nat.pow_le_pow_right (by omega) (by omega)
    have : 2 ^ (Janus.Arm64.clzNat 64 x) ≤ x * 2 ^ (Janus.Arm64.clzNat 64 x) := Nat.le_mul_of_pos_left _ (by omega)
    omega

theorem top_ge (x0 x1 x2 x3 n : Nat) (hx0 : x0 < 2 ^ 64) (hx1 : x1 < 2 ^ 64) (hx2 : x2 < 2 ^ 64) (hx3 : x3 < 2 ^ 64)
    (h0 : x3 ≠ 0) (hn : n = Janus.Arm64.clzNat 64 x3) (v0 v1 v2 v3 : Nat) (hv0 : v0 < 2 ^ 64) (hv1 : v1 < 2 ^ 64)
    (hv2 : v2 < 2 ^ 64) (hv3 : v3 < 2 ^ 64)
    (hv : v0 + 2 ^ 64 * v1 + 2 ^ 128 * v2 + 2 ^ 192 * v3 =
      Fv256.Spec.lsh (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3) n) : 2 ^ 63 ≤ v3 := by
  obtain ⟨hn1, hn2⟩ := clz_norm 64 x3 hx3 h0
  rw [← hn] at hn1 hn2
  unfold Fv256.Spec.lsh Fv256.Spec.W at hv
  simp only [Nat.reducePow, Nat.add_sub_cancel] at hn1 hn2 hv
  have hxs : x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 < 2 ^ 192 := by
    have : 2 ^ 64 * x1 ≤ 2 ^ 64 * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
    have : 2 ^ 128 * x2 ≤ 2 ^ 128 * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  -- P = 2^n divides 2^64
  have hPpos := Nat.two_pow_pos n
  have hn64 : n < 64 := by
    by_cases hh : n < 64
    · exact hh
    · exfalso
      have : 2 ^ 64 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
      have : 2 ^ n ≤ x3 * 2 ^ n := Nat.le_mul_of_pos_left _ (by omega)
      omega
  have hPd : 2 ^ n * 2 ^ (64 - n) = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
  generalize 2 ^ n = P at *
  generalize 2 ^ (64 - n) = Q at *
  -- x3 < Q
  have hxQ : x3 < Q := by
    have : x3 * P < Q * P := by rw [Nat.mul_comm Q P, hPd]; exact hn2
    exact Nat.lt_of_mul_lt_mul_right this
  have hxQ1 : (x3 + 1) * P ≤ 2 ^ 64 := by
    rw [← hPd, Nat.mul_comm P Q]
    exact Nat.mul_le_mul_right P hxQ
  have e1 : (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3) * P = (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2) * P + 2 ^ 192 * (x3 * P) := by
    grind
  have hRP : (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2) * P < 2 ^ 192 * P := Nat.mul_lt_mul_of_pos_right hxs hPpos
  have hlt : (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3) * P < 2 ^ 256 := by
    rw [e1]
    have : 2 ^ 192 * (x3 * P) + 2 ^ 192 * P ≤ 2 ^ 192 * 2 ^ 64 := by
      rw [← Nat.mul_add]
      apply Nat.mul_le_mul_left
      have : (x3 + 1) * P = x3 * P + P := by grind
      omega
    omega
  rw [Nat.mod_eq_of_lt hlt, e1] at hv
  generalize (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2) * P = RP at *
  generalize x3 * P = XP at *
  have hv0' := hv0
  omega

open Fv256.Amd64.LshSum in
/-- `Lsh(z, x, n)` with `n = clz64(x[3])` and `x[3] ≠ 0`: the result's top word is `≥ 2^63` -/
theorem lsh_norm_summary (z x : BitVec 64) :
    Summary Fv256.LshProg.program lshEntry
      (fun s => s.regs 0 = z ∧ s.regs 3 = x ∧ s.xmm 15 = 0 ∧
        (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Disjoint z 32 (s.regs 4) 8 ∧ Disjoint z 32 x 32 ∧
        (s.regs 1).toNat = Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) ∧ s.mem.readLE (x.toNat + 24) 8 ≠ 0)
      (fun s s' => s'.regs 0 = z ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
        valueAt s' z 32 = Spec.lsh (valueAt s x 32) (s.regs 1).toNat ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32)] ∧ 2 ^ 63 ≤ s'.mem.readLE (z.toNat + 24) 8 ∧
        2 ^ 63 / (s'.mem.readLE (z.toNat + 24) 8 / 2 ^ 32) < 2 ^ 64 ∧ s'.mem.readLE (z.toNat + 24) 8 / 2 ^ 32 < 2 ^ 32) := by
  intro s hpc ⟨h0, h3, h15, hra, hzb, hxb, hds, hzx, hn, hx3⟩
  obtain ⟨k, s', hk, hpc', hq⟩ := lsh_summary z x s hpc ⟨h0, h3, h15, hra, hzb, hxb, hds, hzx⟩
  refine ⟨k, s', hk, hpc', hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1, hq.2.2.2.2.2.1, hq.2.2.2.2.2.2.1,
    hq.2.2.2.2.2.2.2.1, hq.2.2.2.2.2.2.2.2, ?_⟩
  have hv := hq.2.2.2.2.2.2.2.1
  simp only [valueAt, Util.readLE_32] at hv
  have htop : 2 ^ 63 ≤ s'.mem.readLE (z.toNat + 24) 8 :=
    top_ge _ _ _ _ _ (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) hx3 hn
      _ _ _ _ (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) hv
  refine ⟨htop, ?_, ?_⟩
  rotate_left
  · have := Util.readLE8_lt s'.mem (z.toNat + 24)
    omega
  have h1 : 2 ^ 31 ≤ s'.mem.readLE (z.toNat + 24) 8 / 2 ^ 32 := by
    apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos 32)).2
    omega
  have h2 : 2 ^ 63 / (s'.mem.readLE (z.toNat + 24) 8 / 2 ^ 32) ≤ 2 ^ 63 / 2 ^ 31 :=
    Nat.div_le_div_left h1 (Nat.two_pow_pos 31)
  have h3 : 2 ^ 63 / 2 ^ 31 = 2 ^ 32 := by decide
  omega

end Fv256.Amd64.LshNorm
