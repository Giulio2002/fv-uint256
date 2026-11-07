import Fv256.Amd64.ScanSfd

/-!
# `scanScientificFromString`: the second `SetFromDecimal` call (receiver = the local exponent `Int`) (Extracted-free)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanSfd

namespace Fv256.Amd64.ScanSfd2

variable (C : SfdCfg)

set_option maxRecDepth 100000

/-- `TopPre` of `SetFromDecimal(&exp, p', n')` called from the frame after the mantissa call (`S4`, `Inv4`) and the stores that zero the
local `exp` (`sp - 40 .. sp - 8`) and push the return address -/
theorem call_pre2 {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {dst p n z' p' n' : BitVec 64} {s S4 S3 : State}
    (hp : TopPre0 C R R2 T b L lo hi dst p n s) (hlo : lo + 4920 ≤ (s.regs 4).toNat) (hEnv4 : Env C R R2 T b L lo ((s.regs 4).toNat - 88) S4)
    (hMF4 : MemFrame s.mem S4.mem [(lo, hi), (dst.toNat, dst.toNat + 32)])
    (hF1 : MemFrame S4.mem S3.mem [(lo, hi)])
    (hr4s4 : S4.regs 4 = s.regs 4 - 112#64) (h14s4 : S4.regs 14 = s.regs 14) (hx4 : S4.xmm 15 = 0) (hdf4 : S4.df = false)
    (hret : S3.mem.readLE ((s.regs 4).toNat - 120) 8 < 2 ^ 47)
    (h4 : S3.regs 4 = s.regs 4 - 120#64) (h0 : S3.regs 0 = z') (hz : z'.toNat = (s.regs 4).toNat - 40)
    (h3 : S3.regs 3 = p') (h1 : S3.regs 1 = n') (h14 : S3.regs 14 = s.regs 14) (hx15 : S3.xmm 15 = 0) (hdf : S3.df = false)
    (hsub1 : p.toNat ≤ p'.toNat) (hsub2 : p'.toNat + n'.toNat ≤ p.toNat + n.toNat) :
    TopPre C R R2 T b L lo ((s.regs 4).toNat - 88) z' p' n' S3 := by
  have hp0 := hp
  obtain ⟨-, -, -, hMod, hEnv, hlo4, hhi, -⟩ := hp0
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, -⟩ := hEnv'
  have hsp := (s.regs 4).isLt
  have hs4 : (S3.regs 4).toNat = (s.regs 4).toNat - 120 := by
    rw [h4, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hF2 : MemFrame s.mem S3.mem [(lo, hi), (dst.toNat, dst.toNat + 32)] :=
    hMF4.trans (hF1.mono (fun a k h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; exact h.1))
      (rs'' := [(lo, hi), (dst.toNat, dst.toNat + 32)]) (fun a k h => ⟨h, h⟩)
  have hE3 : Env C R R2 T b L lo ((s.regs 4).toNat - 88) S3 :=
    env_sub2 C hMod hEnv hEnv4 hF1 (by rw [h14, h14s4]) h14s4 (by omega) (by omega) (by omega) (by omega)
  have hz48 : z'.toNat + 32 ≤ 2 ^ 48 := by omega
  have hzin : lo ≤ z'.toNat ∧ z'.toNat + 32 ≤ (s.regs 4).toNat := by omega
  refine ⟨?_, toppre_sub C hp (by omega) hF2 hE3 h0 h3 h1 (by omega) (by omega) hsub1 hsub2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · unfold RetOK
    rw [hs4, hF1.accessible]
    refine ⟨?_, ?_, hx15, hdf⟩
    · rw [hMF4.accessible]
      exact Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inl rfl) (by omega) (by omega)
    · exact hret
  · intro a k h
    simp only [outside_cons, outside_nil, and_true] at h ⊢
    omega
  · refine ⟨hz48, ?_⟩
    rw [hF1.accessible, hMF4.accessible]
    exact Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)
  · omega
  · exact Or.inl (Outside.of_sub e9 (by omega) (by omega))
  · exact Outside.of_sub e10 (by omega) (by omega)
  · intro r hr
    have := e14 r hr
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega
  · rw [h14]; omega
  · by_cases h0' : n'.toNat = 0
    · exact Or.inl h0'
    · rcases hp.pwin with h | h | h
      · omega
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))

theorem mask_pos (m x : BitVec 64) (h : 0 < m.toNat) (h2 : m.toNat < 2^63) : (0#64 - m).sshiftRight 63 &&& x = x := by
  have hm : (0#64 - m).msb = true := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_sub]; simp; omega
  have : (0#64 - m).sshiftRight 63 = -1 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sshiftRight]
    simp only [hm]
    simp
    have h0 : (18446744073709551615 - (18446744073709551616 - m.toNat) % 18446744073709551616) >>> 63 = 0 := by
      rw [Nat.shiftRight_eq_div_pow]; omega
    rw [h0]
  rw [this]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and]
  have := x.isLt
  rw [Nat.and_comm, show (18446744073709551615:Nat) = 2^64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt this

theorem mask_zero (x : BitVec 64) : (0#64 - 0#64).sshiftRight 63 &&& x = 0 := by simp

/-- the arguments `(p + off, n - (i+1))` of the second call when the exponent text is non-empty -/
theorem args_pos (p n : BitVec 64) (i : Nat) (hpn : p.toNat + n.toNat ≤ 2 ^ 48) (hi : i + 1 < n.toNat) :
    (n - BitVec.ofNat 64 (i + 1)).toNat = n.toNat - (i + 1) ∧
    (p + ((0#64 - (n - BitVec.ofNat 64 (i + 1))).sshiftRight 63 &&& BitVec.ofNat 64 (i + 1))).toNat = p.toNat + (i + 1) := by
  have hn64 := n.isLt
  have h1 : (n - BitVec.ofNat 64 (i + 1)).toNat = n.toNat - (i + 1) := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have : (i + 1) % 2 ^ 64 = i + 1 := Nat.mod_eq_of_lt (by omega)
    rw [this]; omega
  refine ⟨h1, ?_⟩
  rw [mask_pos _ _ (by omega) (by omega)]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : (i + 1) % 2 ^ 64 = i + 1 := Nat.mod_eq_of_lt (by omega)
  rw [this]; exact Nat.mod_eq_of_lt (by omega)

/-- ... and when it is empty -/
theorem args_zero (p n : BitVec 64) (i : Nat) (hi : i + 1 = n.toNat) :
    (n - BitVec.ofNat 64 (i + 1)) = 0 ∧
    (p + ((0#64 - (n - BitVec.ofNat 64 (i + 1))).sshiftRight 63 &&& BitVec.ofNat 64 (i + 1))) = p := by
  have h1 : n - BitVec.ofNat 64 (i + 1) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := n.isLt
    have : (i + 1) % 2 ^ 64 = i + 1 := Nat.mod_eq_of_lt (by omega)
    rw [this]; simp; omega
  refine ⟨h1, ?_⟩
  rw [h1]; have := mask_zero (BitVec.ofNat 64 (i + 1)); simp at this ⊢

end Fv256.Amd64.ScanSfd2
