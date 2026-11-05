import Extracted
import Fv256.SpecE
import Fv256.UtilE
import Fv256.Amd64.DecA
import Fv256.Amd64.DecT
import Fv256.Amd64.DecIter

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E

namespace Fv256.Amd64.Dec

/-- After the loop: `XORL AX, AX` before `slicebytetostring`, `0x2e9` bytes into `Dec`. -/
abbrev decX : Nat := Extracted.entry + 0x2e9

set_option maxHeartbeats 8000000 in
/-- The `JNE` of the loop when the quotient is zero: falls through to `decX`. -/
theorem dec_br_exit (S : State) (hpc : S.rip = BitVec.ofNat 64 decBr) (pf sf : Option Bool)
    (hfl : S.flags = { cf := some false, pf := pf, af := none, zf := some true, sf := sf, ovf := some false }) :
    ReachesRet Extracted.program (BitVec.ofNat 64 decX) S
      (fun S' => S'.regs = S.regs ∧ S'.mem = S.mem ∧ S'.xmm = S.xmm ∧ S'.df = S.df) := by
  have hc : decE + 0x5000 < 2 ^ 47 := by decide
  janus64_run until [decX]
  exact ReachesRet.done (by rfl) ⟨rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 8000000 in
/-- The `JNE` when the quotient is non-zero: the loop-back block ends at the loop head with `pos - 19`. -/
theorem dec_br_loop (S : State) (hpc : S.rip = BitVec.ofNat 64 decBr) (pf sf : Option Bool) (pos b : Nat)
    (hpos : 19 ≤ pos) (hpos2 : pos ≤ 98)
    (hfl : S.flags = { cf := some false, pf := pf, af := none, zf := some false, sf := sf, ovf := some false })
    (e0 : S.regs 0 = BitVec.ofNat 64 (b + 67)) (e1 : S.regs 1 = 19#64) (e11 : S.regs 11 = BitVec.ofNat 64 pos)
    (e4 : S.regs 4 = BitVec.ofNat 64 b) (hb : b + 0x180 ≤ 2 ^ 48) :
    ReachesRet Extracted.program (BitVec.ofNat 64 decH) S
      (fun S' => S'.regs 0 = BitVec.ofNat 64 (pos - 19) ∧ S'.regs 2 = BitVec.ofNat 64 (b + 67) ∧
        S'.regs 7 = BitVec.ofNat 64 (b + 280) ∧ S'.regs 9 = BitVec.ofNat 64 (b + 312) ∧
        (∀ k, k ∉ [0, 2, 7, 9, 11, 12] → S'.regs k = S.regs k) ∧ S'.mem = S.mem ∧ S'.xmm = S.xmm ∧ S'.df = S.df) := by
  have hc : decE + 0x5000 < 2 ^ 47 := by decide
  janus64_run [e0, e1, e11, e4] until [decH]
  refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [setRegF]; exact Fv256.E.ofNat_sub_ofNat pos 19 hpos (by omega)
  · simp [setRegF]
  · simp [setRegF]; exact (BitVec.ofNat_add b 280).symm
  · simp [setRegF]; exact (BitVec.ofNat_add b 312).symm
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [setRegF, hk]

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
set_option profiler true in
set_option profiler.threshold 3000 in
/-- The whole loop of `Dec`, from the head with `t` completed iterations to `decX`. -/
theorem dec_loop (b z g : Nat) (M0 : Memory) (hz0 : 2 ^ 64 ≤ z) (hz1 : z < 2 ^ 256)
    (hb : 0x1a0 ≤ b) (hb8 : b % 8 = 0) (hb2 : b + 0x180 ≤ 2 ^ 48)
    (hw : M0.accessible (b - 0x1a0) (0x1a0 + 0x180) true = true)
    (hg3 : M0.readLE (g + 16) 8 + 0x200 < b) (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M0.accessible (g + 16) 8 false = true)
    (hgd : g + 16 + 8 ≤ b - 0x1a0 ∨ b + 0x180 ≤ g + 16) :
    ∀ y t (s : State), y = z / 10 ^ (19 * t) → y ≠ 0 →
      s.rip = BitVec.ofNat 64 decH → s.regs 0 = BitVec.ofNat 64 (98 - 19 * t) → s.regs 1 = 19#64 →
      s.regs 2 = BitVec.ofNat 64 (b + 67) → s.regs 4 = BitVec.ofNat 64 b → s.regs 5 = BitVec.ofNat 64 (b + 368) →
      s.regs 7 = BitVec.ofNat 64 (b + 280) → s.regs 9 = BitVec.ofNat 64 (b + 312) → s.regs 14 = BitVec.ofNat 64 g →
      s.xmm 15 = 0 → s.df = false → MemFrame M0 s.mem [(b - 0x1a0, b + 368)] →
      Fv256.B.wv s.mem (b + 280) 4 = y → Fv256.B.wv s.mem (b + 312) 4 = 10 ^ 19 →
      (∀ k, k < 19 * t → s.mem.readLE (b + 86 + 97 - k) 1 = 48 + z / 10 ^ k % 10) →
      (∀ k, 19 * t ≤ k → k < 98 → s.mem.readLE (b + 86 + 97 - k) 1 = 48) → TabsOK s.mem →
      ReachesRet Extracted.program (BitVec.ofNat 64 decX) s
        (fun S' => S'.regs 2 = BitVec.ofNat 64 (b + 86 + (98 - decLen z)) ∧ S'.regs 13 = BitVec.ofNat 64 (decLen z) ∧
          S'.regs 4 = BitVec.ofNat 64 b ∧ S'.regs 5 = BitVec.ofNat 64 (b + 368) ∧ S'.regs 14 = BitVec.ofNat 64 g ∧
          S'.xmm 15 = 0 ∧ S'.df = false ∧ MemFrame M0 S'.mem [(b - 0x1a0, b + 368)] ∧
          (∀ k, k < decLen z → S'.mem.readLE (b + 86 + 97 - k) 1 = 48 + z / 10 ^ k % 10) ∧ TabsOK S'.mem) := by
  intro y
  induction y using Nat.strongRecOn with
  | _ y ih =>
    intro t s hy hy0 hrip e0 e1 e2 e4 e5 e7 e9 e14 hx15 hdf hfm hym hdm hout1 hout2 htab
    have ht4 : t ≤ 4 := Nat.le_of_not_lt (fun hc => by
      have h1 : 10 ^ 95 ≤ 10 ^ (19 * t) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : z / 10 ^ (19 * t) = 0 := Nat.div_eq_of_lt (by
        have : (2:Nat) ^ 256 < 10 ^ 95 := by decide
        omega)
      omega)
    have hwS : s.mem.accessible (b - 0x1a0) (0x1a0 + 0x180) true = true := by rw [hfm.accessible]; exact hw
    have hg3S : s.mem.readLE (g + 16) 8 + 0x200 < b := by
      rw [hfm.readLE _ _ (by simp only [Outside, and_true]; omega)]; exact hg3
    have hg2S : s.mem.accessible (g + 16) 8 false = true := by rw [hfm.accessible]; exact hg2
    have hit := dec_iter s b (98 - 19 * t) y s.mem hrip rfl hy0 (by rw [hy]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hz1) (by omega) (by omega) hb hb8 hb2 hwS htab hx15 hdf
      e0 e1 e2 e7 e9 e4 e5 (by rw [e14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hg3S)
      (by rw [e14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
      (by rw [e14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hg2S)
      (by rw [e14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hgd) hym hdm
    have hz10 : 10 ^ (19 * t) ≤ z := Nat.le_of_not_lt (fun hc => by
      have : z / 10 ^ (19 * t) = 0 := Nat.div_eq_of_lt hc
      omega)
    have hpow : ∀ t' : Nat, 10 ^ (19 * (t' + 1)) = 10 ^ (19 * t') * 10 ^ 19 := fun t' => by
      rw [← Nat.pow_add]; congr 1
    have hy19 : z / 10 ^ (19 * (t + 1)) = y / 10 ^ 19 := by
      rw [hy, Nat.div_div_eq_div_mul, hpow]
    have hfm2 : ∀ S2 : State, MemFrame s.mem S2.mem [(b - 0x1a0, b + 86), (b + (98 - 19 * t - decLen (y % 10 ^ 19)) + 86, b + 86 + (98 - 19 * t)), (b + 184, b + 368)] →
        MemFrame M0 S2.mem [(b - 0x1a0, b + 368)] := by
      intro S2 hf
      refine hfm.trans (hf.mono ?_) (fun a n h => ⟨h, h⟩)
      intro a n h
      simp only [Outside, and_true] at h ⊢
      omega
    refine Fv256.E.reachesRet_bind' hit ?_
    rintro S' hrip' ⟨r0, r1, r2, r4, r5, r11, r13, r14, rx, rdf, ⟨pf, sf, hfl⟩, hy', hd', hdig, hfr, htab'⟩
    have hnd19 : decLen (y % 10 ^ 19) ≤ 19 := decLen_le_of_lt_pow _ 19 (by decide) (Nat.mod_lt _ (by decide))
    have hnd1 := decLen_pos (y % 10 ^ 19)
    have hfrM : MemFrame M0 S'.mem [(b - 0x1a0, b + 368)] := hfm2 S' hfr
    by_cases h0 : y / 10 ^ 19 = 0
    · -- the last chunk
      have hzf : decide (y / 10 ^ 19 = 0) = true := by simp [h0]
      rw [hzf] at hfl
      refine ReachesRet.mono (dec_br_exit S' hrip' pf sf hfl) ?_
      rintro S'' ⟨hrg, hmem, hxm, hdf'⟩
      have hy10 : y < 10 ^ 19 := by
        have := Nat.div_eq_zero_iff.mp h0
        omega
      have hnd : decLen (y % 10 ^ 19) = decLen y := by rw [Nat.mod_eq_of_lt hy10]
      have hL : decLen z = decLen (y % 10 ^ 19) + 19 * t := by
        rw [decLen_div_pow z (19 * t) hz10, ← hy, hnd]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hrg, r2]; congr 1; omega
      · rw [hrg, r13]; congr 1; omega
      · rw [hrg]; exact r4
      · rw [hrg]; exact r5
      · rw [hrg, r14, e14]
      · rw [hxm]; exact rx
      · rw [hdf']; exact rdf
      · rw [hmem]; exact hfrM
      · intro k hk
        rw [hmem]
        by_cases hk1 : k < 19 * t
        · rw [hfr.readLE _ _ (by simp only [Outside, and_true]; omega), hout1 k hk1]
        · have hk2 : k - 19 * t < decLen (y % 10 ^ 19) := by omega
          have := hdig (k - 19 * t) hk2
          rw [show b + 86 + (98 - 19 * t) - 1 - (k - 19 * t) = b + 86 + 97 - k by omega, this, hy,
            Nat.div_div_eq_div_mul, ← Nat.pow_add, show 19 * t + (k - 19 * t) = k by omega]
      · rw [hmem]; exact htab'
    · -- another chunk
      sorry
end Fv256.Amd64.Dec
