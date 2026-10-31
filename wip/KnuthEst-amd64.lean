import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.Amd64.KnuthSub

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.KnuthSub

namespace Fv256.Amd64.KnuthEst

macro "div2_close2 " v:ident rem:ident uk:ident d:ident hvB:ident hukB:ident hd1:ident hd2:ident hrem:ident : tactic =>
  `(tactic| (
    unfold Fv256.B.div2by1
    have hPB : $v * $rem < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' $hvB (by omega)
    have hPB2 : $v * $rem / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul hPB
    simp only [Nat.reducePow]
    generalize $v * $rem = P at *
    have hPm : P / 2 ^ 64 % 2 ^ 64 = P / 2 ^ 64 := Nat.mod_eq_of_lt hPB2
    simp only [Nat.reducePow] at hPm hPB2 $hukB $hd2 $hd1
    have hX : (P / 18446744073709551616 + $rem + (P % 18446744073709551616 + $uk) / 18446744073709551616 + 1) % 18446744073709551616 =
        ((P / 18446744073709551616 + $rem + (P % 18446744073709551616 + $uk) / 18446744073709551616) % 18446744073709551616 + 1) % 18446744073709551616 := by
      omega
    simp only [hPm]
    rw [hX]
    repeat' split
    all_goals omega))

set_option maxHeartbeats 8000000 in
theorem est1 (s0 : State) (up dp n m j : Nat) (v dl dh u2 u1 u0 : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hn : 2 ≤ n) (hn2 : n < 2 ^ 20) (hm : j + n + 1 ≤ m) (hm2 : m < 2 ^ 20)
    (hdh : 2 ^ 63 ≤ dh) (hdh2 : dh < 2 ^ 64) (hdl : dl < 2 ^ 64)
    (hv : v + 2 ^ 64 = (2 ^ 64 * 2 ^ 64 - 1) / dh)
    (hs : (R 4).toNat + 0x90 ≤ 2 ^ 48)
    (hMs : M.accessible (R 4).toNat 0x90 true = true)
    (hua : M.accessible up (8 * m) true = true) (hub : up + 8 * m ≤ 2 ^ 48)
    (hda : M.accessible dp (8 * n) false = true) (hdb : dp + 8 * n ≤ 2 ^ 48)
    (hsu : up + 8 * m ≤ (R 4).toNat ∨ (R 4).toNat + 0x90 ≤ up) (hsd : dp + 8 * n ≤ (R 4).toNat ∨ (R 4).toNat + 0x90 ≤ dp)
    (hlt : u2 < dh)
    (hcap : m ≤ (R 8).toNat)
    (e0 : R 0 = BitVec.ofNat 64 v) (e6 : R 6 = BitVec.ofNat 64 j) (e7 : R 7 = BitVec.ofNat 64 up) (e9 : R 9 = BitVec.ofNat 64 dp)
    (e10 : R 10 = BitVec.ofNat 64 n) (e11 : R 11 = BitVec.ofNat 64 dl) (e13 : R 13 = BitVec.ofNat 64 m)
    (e15 : R 15 = BitVec.ofNat 64 dh) (e1 : R 1 = BitVec.ofNat 64 (n - 1))
    (hu2 : M.readLE (up + (j + n) * 8) 8 = u2) (hu1 : M.readLE (up + (j + (n - 1)) * 8) 8 = u1) (hu0 : M.readLE (up + (j + (n - 2)) * 8) 8 = u0) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (kn + 0x17d))
      { s0 with regs := R, rip := BitVec.ofNat 64 (kn + 0xd1), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (kn + 0x17d), flags := fl', mem := M' } ∧
        R' 0 = BitVec.ofNat 64 ((u2 * 2 ^ 64 + u1) / dh) ∧ R' 2 = BitVec.ofNat 64 ((u2 * 2 ^ 64 + u1) % dh) ∧
        R' 3 = BitVec.ofNat 64 u0 ∧ R' 9 + R' 12 = R' 0 ∧
        (∀ k, k ∉ [0, 2, 3, 9, 12] → R' k = R k) ∧
        M'.readLE ((R 4).toNat + 8) 8 = (R' 2).toNat ∧ M'.readLE ((R 4).toNat + 0x18) 8 = (R' 0).toNat ∧
        M'.readLE (R 4).toNat 8 = u2 ∧ M'.readLE ((R 4).toNat + 0x38) 8 = j + n ∧
        MemFrame M M' [((R 4).toNat, (R 4).toNat + 0x10), ((R 4).toNat + 0x18, (R 4).toNat + 0x30), ((R 4).toNat + 0x38, (R 4).toNat + 0x40)]) := by
  have hcode := kn_lt
  have hjb : (BitVec.ofNat 64 j).toNat = j := by rw [BitVec.toNat_ofNat]; omega
  have hnsgn : ¬ (BitVec.ofNat 64 j).msb = true := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat]; simp; omega
  have hvB : v < 2 ^ 64 := Fv256.B.recip_lt dh v hdh hv
  have hu1B : u1 < 2 ^ 64 := by
    rw [← hu1]; have := Janus.Arm64.Memory.readLE_lt M (up + (j + (n - 1)) * 8) 8; simpa using this
  have hvm : v % 18446744073709551616 = v := Nat.mod_eq_of_lt hvB
  have hcorr := Fv256.B.div2by1_correct (2 ^ 64) dh (v + 2 ^ 64) u2 u1 (by omega) hdh2 (by rw [← hv]) hlt hu1B
  have hsub : v + 2 ^ 64 - 2 ^ 64 = v := by omega
  rw [hsub] at hcorr
  have hrem : u2 < dh := hlt
  have hdm : dh % 18446744073709551616 = dh := Nat.mod_eq_of_lt hdh2
  have hu1m : u1 % 18446744073709551616 = u1 := Nat.mod_eq_of_lt hu1B
  have hu2m : u2 % 18446744073709551616 = u2 := Nat.mod_eq_of_lt (by omega)
  have hd1 := hdh
  have hd2 := hdh2
  have hukB := hu1B
  janus64_run [e0, e6, e7, e9, e10, e11, e13, e15, e1, hnsgn, hu2, hu1, hu0, hlt]
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (config := { decide := true }) only [setRegF, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, Nat.reducePow, apply_ite BitVec.toNat, hvm, hdm, hu1m, hu2m]
    rw [show (u2 * 2 ^ 64 + u1) / dh = (Fv256.B.div2by1 (2 ^ 64) dh v u2 u1).1 from (congrArg Prod.fst hcorr).symm]
    have key := Fv256.B.Qmach_eq dh (v + 2 ^ 64) v u2 u1 hd1 hd2 (by rw [← hv]) rfl hrem hukB
    unfold Fv256.B.Qmach at key
    rw [← key]
    have hc : (decide (18446744073709551616 ≤ v * u2 % 18446744073709551616 + u1)).toNat = (v * u2 % 18446744073709551616 + u1) / 18446744073709551616 := by
      have hh : v * u2 % 18446744073709551616 < 18446744073709551616 := Nat.mod_lt _ (by omega)
      by_cases h : 18446744073709551616 ≤ v * u2 % 18446744073709551616 + u1
      · simp only [h, decide_true, Bool.toNat_true]; omega
      · simp only [h, decide_false, Bool.toNat_false]; omega
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, apply_ite BitVec.toNat, hc, hu1m, Nat.mod_mod]
    have hm32 : ∀ x : Nat, x % 4294967296 % 18446744073709551616 = x % 4294967296 := fun x =>
      Nat.mod_eq_of_lt (by have := Nat.mod_lt x (show 0 < 4294967296 by decide); omega)
    rw [Nat.add_comm (v * u2 / 18446744073709551616 % 18446744073709551616) u2]
    simp only [Nat.reduceMod, hm32]
  · simp (config := { decide := true }) only [setRegF, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, Nat.reducePow, apply_ite BitVec.toNat, hvm, hdm, hu1m, hu2m]
    rw [show (u2 * 2 ^ 64 + u1) % dh = (Fv256.B.div2by1 (2 ^ 64) dh v u2 u1).2 from (congrArg Prod.snd hcorr).symm]
    have hr2 : (Fv256.B.div2by1 (2 ^ 64) dh v u2 u1).2 < 18446744073709551616 := by
      rw [hcorr]; exact Nat.lt_trans (Nat.mod_lt _ (by omega)) hdh2
    rw [Nat.mod_eq_of_lt hr2]
    have key := Fv256.B.Rmach_eq dh (v + 2 ^ 64) v u2 u1 hd1 hd2 (by rw [← hv]) rfl hrem hukB
    unfold Fv256.B.Rmach at key
    rw [← key]
    have hc : (decide (18446744073709551616 ≤ v * u2 % 18446744073709551616 + u1)).toNat = (v * u2 % 18446744073709551616 + u1) / 18446744073709551616 := by
      have hh : v * u2 % 18446744073709551616 < 18446744073709551616 := Nat.mod_lt _ (by omega)
      by_cases h : 18446744073709551616 ≤ v * u2 % 18446744073709551616 + u1
      · simp only [h, decide_true, Bool.toNat_true]; omega
      · simp only [h, decide_false, Bool.toNat_false]; omega
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, apply_ite BitVec.toNat, hc, hu1m, Nat.mod_mod]
    rw [Nat.add_comm (v * u2 / 18446744073709551616 % 18446744073709551616) u2]
  · simp [setRegF]
  · simp (config := { decide := true }) only [setRegF, ↓reduceIte]
    exact BitVec.add_comm _ _
  · intro k hk
    have hk' : k ≠ 0 ∧ k ≠ 2 ∧ k ≠ 3 ∧ k ≠ 9 ∧ k ≠ 12 := by simpa using hk
    obtain ⟨k0, k2, k3, k9, k12⟩ := hk'
    simp [setRegF, k0, k2, k3, k9, k12]
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simp (config := { decide := true }) only [setRegF, ↓reduceIte, Nat.reducePow]
    exact Nat.mod_eq_of_lt (BitVec.isLt _)
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simp (config := { decide := true }) only [setRegF, ↓reduceIte, Nat.reducePow]
    have h8 : ∀ b : BitVec 8, b.toNat % 4294967296 = b.toNat := fun b => Nat.mod_eq_of_lt (by have := b.isLt; omega)
    have hm32 : ∀ x : Nat, x % 4294967296 % 18446744073709551616 = x % 4294967296 := fun x =>
      Nat.mod_eq_of_lt (by have := Nat.mod_lt x (show 0 < 4294967296 by decide); omega)
    simp only [apply_ite BitVec.toNat, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_setWidth, Nat.mod_mod, h8, hm32]
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega)
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega)
  · exact ((((((MemFrame.refl _ _).writeLE _ (r := ((R 4).toNat + 0x38, (R 4).toNat + 0x40)) (by simp) (by omega) (by omega)).writeLE _
      (r := ((R 4).toNat, (R 4).toNat + 0x10)) (by simp) (by omega) (by omega)).writeLE _
      (r := ((R 4).toNat + 0x18, (R 4).toNat + 0x30)) (by simp) (by omega) (by omega)).writeLE _
      (r := ((R 4).toNat, (R 4).toNat + 0x10)) (by simp) (by omega) (by omega)).writeLE _
      (r := ((R 4).toNat + 0x18, (R 4).toNat + 0x30)) (by simp) (by omega) (by omega))

set_option maxHeartbeats 8000000 in
theorem est2 (s0 : State) (up dp n m j v dl dh u2 u0 Q r : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hn : 2 ≤ n) (hn2 : n < 2 ^ 20) (hm : j + n + 1 ≤ m) (hm2 : m < 2 ^ 20)
    (hQ : Q < 2 ^ 64) (hr : r < 2 ^ 64) (hdl : dl < 2 ^ 64) (hu0 : u0 < 2 ^ 64)
    (hs : (R 4).toNat + 0x90 ≤ 2 ^ 48)
    (hMs : M.accessible (R 4).toNat 0x90 true = true)
    (hua : M.accessible up (8 * m) true = true) (hub : up + 8 * m ≤ 2 ^ 48)
    (hda : M.accessible dp (8 * n) false = true) (hdb : dp + 8 * n ≤ 2 ^ 48)
    (hsu : up + 8 * m ≤ (R 4).toNat ∨ (R 4).toNat + 0x90 ≤ up) (hsd : dp + 8 * n ≤ (R 4).toNat ∨ (R 4).toNat + 0x90 ≤ dp)
    (hcap : m ≤ (R 8).toNat) (hcapB : (R 8).toNat < 2 ^ 55)
    (e0 : R 0 = BitVec.ofNat 64 Q) (e2 : R 2 = BitVec.ofNat 64 r) (e3 : R 3 = BitVec.ofNat 64 u0)
    (e6 : R 6 = BitVec.ofNat 64 j) (e7 : R 7 = BitVec.ofNat 64 up) (e1 : R 1 = BitVec.ofNat 64 (n - 1))
    (e10 : R 10 = BitVec.ofNat 64 n) (e11 : R 11 = BitVec.ofNat 64 dl) (e13 : R 13 = BitVec.ofNat 64 m)
    (e912 : R 9 + R 12 = R 0)
    (hm8 : M.readLE ((R 4).toNat + 8) 8 = r) (hm18 : M.readLE ((R 4).toNat + 0x18) 8 = Q)
    (hm0 : M.readLE (R 4).toNat 8 = u2) (hm10 : M.readLE ((R 4).toNat + 0x10) 8 = v)
    (hm88 : M.readLE ((R 4).toNat + 0x88) 8 = dp) (hm30 : M.readLE ((R 4).toNat + 0x30) 8 = dl) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (kn + 0x235))
      { s0 with regs := R, rip := BitVec.ofNat 64 (kn + 0x17d), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (kn + 0x235), flags := fl', mem := M' } ∧
        R' 0 = BitVec.ofNat 64 v ∧ R' 1 = BitVec.ofNat 64 (n - 1) ∧ R' 2 = BitVec.ofNat 64 u2 ∧
        R' 3 = BitVec.ofNat 64 (if r * 2 ^ 64 + u0 < Q * dl then Q - 1 else Q) ∧
        R' 6 = BitVec.ofNat 64 (up + 8 * j) ∧ R' 9 = BitVec.ofNat 64 dp ∧ R' 11 = 0 ∧ R' 12 = BitVec.ofNat 64 m ∧ R' 13 = 0 ∧
        (∀ k, k ∉ [0, 1, 2, 3, 6, 9, 11, 12, 13] → R' k = R k) ∧
        M'.readLE ((R 4).toNat + 0x28) 8 = j ∧
        MemFrame M M' [((R 4).toNat + 0x28, (R 4).toNat + 0x30)]) := by
  have hcode := kn_lt
  have hjb : (BitVec.ofNat 64 j).toNat = j := by rw [BitVec.toNat_ofNat]; omega
  have hdec : 1 ≤ Q → R 9 + R 12 - 1#64 = BitVec.ofNat 64 (Q - 1) := by
    intro h1; rw [e912, e0]; bv_omega
  have hsl := Fv256.B.slice_ptr j up (R 8) (by omega) hcapB
  have hQd : Q * dl < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hQ hdl
  janus64_run [e0, e2, e3, e6, e7, e1, e10, e11, e13, hm8, hm18, hm0, hm10, hm88, hm30]
  all_goals refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try (first | (simp [setRegF]; done) | (simp [setRegF, e1]; done) | (simp [setRegF, hsl]; done)))
  all_goals (try (intro k hk; have hk' : k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3 ∧ k ≠ 6 ∧ k ≠ 9 ∧ k ≠ 11 ∧ k ≠ 12 ∧ k ≠ 13 := by simpa using hk
                  obtain ⟨k0, k1, k2, k3, k6, k9, k11, k12, k13⟩ := hk'
                  simp [setRegF, k0, k1, k2, k3, k6, k9, k11, k12, k13]; done))
  all_goals first
    | (simp (config := { decide := true }) only [setRegF, ↓reduceIte]; exact hsl)
    | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]; simp only [Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega))
    | exact (MemFrame.refl _ _).writeLE _ (r := ((R 4).toNat + 0x28, (R 4).toNat + 0x30)) (by simp) (by omega) (by omega)
    | (simp (config := { decide := true }) only [setRegF, ↓reduceIte]
       generalize hP : Q * dl = P at *
       split
       · first | (have hQ1 : 1 ≤ Q := by
                    rcases Nat.eq_zero_or_pos Q with h | h
                    · subst h; simp at hP; omega
                    · exact h
                  rw [hdec hQ1]) | (exfalso; omega)
       · first | rfl | (exfalso; omega))

end Fv256.Amd64.KnuthEst
