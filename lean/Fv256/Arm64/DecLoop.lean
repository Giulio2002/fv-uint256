import Extracted
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.Arm64.DecT
import Fv256.Arm64.DecA
import Fv256.Arm64.DecInit
import Fv256.Arm64.DecIter

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec
open Fv256.E

namespace Fv256.Arm64.Dec

/-- After the loop: `MOVD ZR, R0` before `slicebytetostring`, `0x200` bytes into `Dec`. -/
def decX : Nat := decE + 0x200

set_option maxHeartbeats 8000000 in
/-- The `CBNZ` of the loop when the quotient is zero: falls through to `decX`. -/
theorem dec_br_exit (S : State) (hpc : S.pc = BitVec.ofNat 64 decBr) (hz : S.regs 10 = 0#64) :
    ReachesRet Extracted.program (BitVec.ofNat 64 decX) S
      (fun S' => S'.regs = S.regs ∧ S'.mem = S.mem ∧ S'.sp = S.sp) := by
  have hc : decE + 0x5000 < 2 ^ 47 := by decide
  janus_run [hz] until [decX]
  exact ReachesRet.done (by rfl) ⟨rfl, rfl, rfl⟩

set_option maxHeartbeats 8000000 in
/-- The `CBNZ` when the quotient is non-zero: the loop-back block ends at the loop head with `pos - 19`. -/
theorem dec_br_loop (S : State) (hpc : S.pc = BitVec.ofNat 64 decBr) (pos b : Nat)
    (hpos : 19 ≤ pos) (hpos2 : pos ≤ 98) (hz : S.regs 10 ≠ 0#64)
    (e0 : S.regs 0 = BitVec.ofNat 64 (b + 75)) (e2 : S.regs 2 = 19#64) (e8 : S.regs 8 = BitVec.ofNat 64 pos)
    (esp : S.sp = BitVec.ofNat 64 b) (hb : b + 384 ≤ 2 ^ 48) :
    ReachesRet Extracted.program (BitVec.ofNat 64 decH) S
      (fun S' => S'.regs 0 = BitVec.ofNat 64 (pos - 19) ∧ S'.regs 1 = 19#64 ∧ S'.regs 8 = BitVec.ofNat 64 (b + 75) ∧
        S'.regs 3 = BitVec.ofNat 64 (b + 288) ∧ S'.regs 6 = BitVec.ofNat 64 (b + 320) ∧
        (∀ k, k ∉ [0, 1, 3, 6, 8, 9] → S'.regs k = S.regs k) ∧ S'.mem = S.mem ∧ S'.sp = S.sp) := by
  have hc : decE + 0x5000 < 2 ^ 47 := by decide
  janus_run [hz, e0, e2, e8, esp] until [decH]
  refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setReg, e8]
    simpa using Fv256.E.ofNat_sub_ofNat pos 19 hpos (by omega)
  · simp [setReg]
  · simp [setReg, e0]
  · simp [setReg]; exact (BitVec.ofNat_add b 288).symm
  · simp [setReg]; exact (BitVec.ofNat_add b 320).symm
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setReg, hk]
  · rfl
  · exact esp.symm

theorem arith1 (b t L n : Nat) (hL : L = n + 19 * t) (ht : t ≤ 4) (hn : n ≤ 19) :
    b + (98 - 19 * t - n) + 86 = b + 86 + (98 - L) := by omega
theorem arith2 (t L n : Nat) (hL : L = n + 19 * t) (ht : t ≤ 4) (hn : n ≤ 19) : 98 - (98 - 19 * t - n) = L := by omega

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- The whole loop of `Dec`, from the head with `t` completed iterations to `decX`. -/
theorem dec_loop (b z g : Nat) (M0 : Memory) (hz0 : 2 ^ 64 ≤ z) (hz1 : z < 2 ^ 256)
    (hb : 344 ≤ b) (hb16 : b % 16 = 0) (hb2 : b + 384 ≤ 2 ^ 48)
    (hw : M0.accessible (b - 344) (344 + 384) true = true)
    (hg3 : M0.readLE (g + 16) 8 + 304 < b) (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M0.accessible (g + 16) 8 false = true)
    (hgd : g + 16 + 8 ≤ b - 344 ∨ b + 384 ≤ g + 16) :
    ∀ y t (s : State), y = z / 10 ^ (19 * t) → y ≠ 0 →
      s.pc = BitVec.ofNat 64 decH → s.regs 0 = BitVec.ofNat 64 (98 - 19 * t) → s.regs 1 = 19#64 →
      s.regs 8 = BitVec.ofNat 64 (b + 75) → s.regs 3 = BitVec.ofNat 64 (b + 288) → s.regs 6 = BitVec.ofNat 64 (b + 320) →
      s.sp = BitVec.ofNat 64 b → s.regs 28 = BitVec.ofNat 64 g → MemFrame M0 s.mem [(b - 344, b - 8), (b + 8, b + 384)] →
      Fv256.B.wv s.mem (b + 288) 4 = y → Fv256.B.wv s.mem (b + 320) 4 = 10 ^ 19 →
      (∀ k, k < 19 * t → s.mem.readLE (b + 94 + 97 - k) 1 = 48 + z / 10 ^ k % 10) →
      (∀ k, 19 * t ≤ k → k < 98 → s.mem.readLE (b + 94 + 97 - k) 1 = 48) → TabsOK s.mem →
      ReachesRet Extracted.program (BitVec.ofNat 64 decX) s
        (fun S' => S'.regs 9 = BitVec.ofNat 64 (b + 94 + (98 - decLen z)) ∧ S'.regs 11 = BitVec.ofNat 64 (decLen z) ∧
          S'.sp = BitVec.ofNat 64 b ∧ S'.regs 28 = BitVec.ofNat 64 g ∧ S'.regs 29 = s.regs 29 ∧ S'.regs 18 = s.regs 18 ∧
          MemFrame M0 S'.mem [(b - 344, b - 8), (b + 8, b + 384)] ∧
          (∀ k, k < decLen z → S'.mem.readLE (b + 94 + 97 - k) 1 = 48 + z / 10 ^ k % 10) ∧ TabsOK S'.mem) := by
  intro y
  induction y using Nat.strongRecOn with
  | _ y ih =>
    intro t s hy hy0 hrip e0 e1 e8 e3 e6 esp e28 hfm hym hdm hout1 hout2 htab
    have ht4 : t ≤ 4 := Nat.le_of_not_lt (fun hc => by
      have h1 : 10 ^ 95 ≤ 10 ^ (19 * t) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : z / 10 ^ (19 * t) = 0 := Nat.div_eq_of_lt (by
        have : (2:Nat) ^ 256 < 10 ^ 95 := by decide
        omega)
      omega)
    have hwS : s.mem.accessible (b - 344) (344 + 384) true = true := by rw [hfm.accessible]; exact hw
    have hg3S : s.mem.readLE (g + 16) 8 + 304 < b := by
      rw [hfm.readLE _ _ (by simp only [Outside, and_true]; omega)]; exact hg3
    have hg2S : s.mem.accessible (g + 16) 8 false = true := by rw [hfm.accessible]; exact hg2
    have hit := dec_iter s b (98 - 19 * t) y s.mem hrip rfl hy0 (by rw [hy]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hz1) (by omega) (by omega) hb hb16 hb2 hwS htab
      e0 e1 e8 e3 e6 esp (by rw [e28, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hg3S)
      (by rw [e28, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
      (by rw [e28, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hg2S)
      (by rw [e28, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hgd) hym hdm
    have hz10 : 10 ^ (19 * t) ≤ z := Nat.le_of_not_lt (fun hc => by
      have : z / 10 ^ (19 * t) = 0 := Nat.div_eq_of_lt hc
      omega)
    have hpow : ∀ t' : Nat, 10 ^ (19 * (t' + 1)) = 10 ^ (19 * t') * 10 ^ 19 := fun t' => by
      rw [← Nat.pow_add]; congr 1
    have hy19 : z / 10 ^ (19 * (t + 1)) = y / 10 ^ 19 := by
      rw [hy, Nat.div_div_eq_div_mul, hpow]
    have hfm2 : ∀ S2 : State, MemFrame s.mem S2.mem [(b - 344, b - 8), (b + 8, b + 94), (b + 94 + (98 - 19 * t - decLen (y % 10 ^ 19)), b + 94 + (98 - 19 * t)), (b + 192, b + 384)] →
        MemFrame M0 S2.mem [(b - 344, b - 8), (b + 8, b + 384)] := by
      intro S2 hf
      refine hfm.trans (hf.mono ?_) (fun a n h => ⟨h, h⟩)
      intro a n h
      simp only [Outside, and_true] at h ⊢
      omega
    refine Fv256.E.reachesRet64_bind hit ?_
    rintro S' hrip' ⟨r0, r2, r8, r9, r11, r10, r28, r29, r18, rsp, hy', hd', hdig, hfr, htab'⟩
    have hnd19 : decLen (y % 10 ^ 19) ≤ 19 := decLen_le_of_lt_pow _ 19 (by decide) (Nat.mod_lt _ (by decide))
    have hnd1 := decLen_pos (y % 10 ^ 19)
    have hfrM : MemFrame M0 S'.mem [(b - 344, b - 8), (b + 8, b + 384)] := hfm2 S' hfr
    by_cases h0 : y / 10 ^ 19 = 0
    · -- the last chunk
      have hz10' : S'.regs 10 = 0#64 := r10.2 h0
      refine reachesRet64_mono (dec_br_exit S' hrip' hz10') ?_
      rintro S'' ⟨hrg, hmem, hsp⟩
      have hy10 : y < 10 ^ 19 := by
        have := Nat.div_eq_zero_iff.mp h0
        omega
      have hnd : decLen (y % 10 ^ 19) = decLen y := by rw [Nat.mod_eq_of_lt hy10]
      have hL : decLen z = decLen (y % 10 ^ 19) + 19 * t := by
        rw [decLen_div_pow z (19 * t) hz10, ← hy, hnd]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hrg, r9]; exact congrArg (BitVec.ofNat 64) (by omega)
      · rw [hrg, r11]; exact congrArg (BitVec.ofNat 64) (arith2 t (decLen z) (decLen (y % 10 ^ 19)) hL ht4 hnd19)
      · rw [hsp]; exact rsp.trans esp
      · rw [hrg, r28, e28]
      · rw [hrg, r29]
      · rw [hrg, r18]
      · rw [hmem]; exact hfrM
      · intro k hk
        rw [hmem]
        by_cases hk1 : k < 19 * t
        · rw [hfr.readLE _ _ (by simp only [Outside, and_true]; omega), hout1 k hk1]
        · have hk2 : k - 19 * t < decLen (y % 10 ^ 19) := by omega
          have := hdig (k - 19 * t) hk2
          rw [show b + 94 + (98 - 19 * t) - 1 - (k - 19 * t) = b + 94 + 97 - k by omega] at this
          rw [this, hy,
            Nat.div_div_eq_div_mul, ← Nat.pow_add, show 19 * t + (k - 19 * t) = k by omega]
      · rw [hmem]; exact htab'
    · -- another chunk
      have hz10' : S'.regs 10 ≠ 0#64 := fun h => h0 (r10.1 h)
      have ht3 : t ≤ 3 := Nat.le_of_not_lt (fun hc => by
        have h3 : 10 ^ 95 ≤ 10 ^ (19 * (t + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
        have h5 : (2:Nat) ^ 256 < 10 ^ 95 := by decide
        have h4 : z / 10 ^ (19 * (t + 1)) = 0 := Nat.div_eq_of_lt (by omega)
        have : y / 10 ^ 19 = 0 := by rw [← hy19]; exact h4
        exact h0 this)
      refine Fv256.E.reachesRet64_bind (dec_br_loop S' hrip' (98 - 19 * t) b (by omega) (by omega) hz10' r0 r2 r8 (rsp.trans esp) hb2) ?_
      rintro S'' hrip'' ⟨q0, q1, q8, q3, q6, qk, qm, qsp⟩
      have hym2 : Fv256.B.wv S''.mem (b + 288) 4 = y / 10 ^ 19 := by rw [qm]; exact hy'
      have hdm2 : Fv256.B.wv S''.mem (b + 320) 4 = 10 ^ 19 := by rw [qm]; exact hd'
      refine reachesRet64_mono (ih (y / 10 ^ 19) (Nat.div_lt_self (by omega) (by decide)) (t + 1) S'' hy19.symm h0 hrip'' ?_ q1 q8 q3 q6 ?_ ?_ ?_ hym2 hdm2 ?_ ?_ ?_) ?_
      · rw [q0]; exact congrArg (BitVec.ofNat 64) (show 98 - 19 * t - 19 = 98 - 19 * (t + 1) by omega)
      · rw [qsp]; exact rsp.trans esp
      · rw [qk 28 (by simp)]; rw [r28, e28]
      · rw [qm]; exact hfrM
      · intro k hk
        rw [qm]
        by_cases hk1 : k < 19 * t
        · rw [hfr.readLE _ _ (by simp only [Outside, and_true]; omega), hout1 k hk1]
        · by_cases hk3 : k - 19 * t < decLen (y % 10 ^ 19)
          · have := hdig (k - 19 * t) hk3
            rw [show b + 94 + (98 - 19 * t) - 1 - (k - 19 * t) = b + 94 + 97 - k by omega] at this
            rw [this, hy, Nat.div_div_eq_div_mul, ← Nat.pow_add, show 19 * t + (k - 19 * t) = k by omega]
          · rw [hfr.readLE _ _ (by simp only [Outside, and_true]; omega), hout2 k (by omega) (by omega)]
            have hlt := decLen_lt_pow (y % 10 ^ 19)
            have hz0 : y % 10 ^ 19 / 10 ^ (k - 19 * t) = 0 :=
              Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega)))
            have := Fv256.E.digit_mod y (k - 19 * t) 19 (by omega)
            rw [hz0] at this
            rw [hy, Nat.div_div_eq_div_mul, ← Nat.pow_add, show 19 * t + (k - 19 * t) = k by omega] at this
            omega
      · intro k hk1 hk2
        rw [qm]
        rw [hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]
        exact hout2 k (by omega) hk2
      · rw [qm]; exact htab'
      · rintro Sf ⟨f1, f2, f3, f4, f5, f5', f6, f7, f8⟩
        refine ⟨f1, f2, f3, f4, ?_, ?_, f6, f7, f8⟩
        · rw [f5, qk 29 (by simp), r29]
        · rw [f5', qk 18 (by simp), r18]
end Fv256.Arm64.Dec
