import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.UtilD

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float Janus.Amd64.FP

namespace Fv256.Amd64.Float64

set_option maxHeartbeats 8000000 in
theorem lem0 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => (StackGuardOK s 0 ∧ StackWritable s 80 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 80 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧ GoMXCSR s) ∧
        (s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0))
      (fun s s' => (s'.xmm 0).toNat % 2 ^ 64 = Fv256.B.float64BitsNearest (valueAt s x 32) ∧
        MemFrame s.mem s'.mem [((s.regs regSP).toNat - 80, (s.regs regSP).toNat + 8)]) := by
  intro ret hret s hs ⟨⟨hg, ⟨hlow, hnw, hacc⟩, ⟨hxw, hx⟩, hds, hm⟩, h3, h2, h1⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2
  simp only [regSP] at hacc hlow hnw hds
  simp only [valueAt]
  have hx0 := Util.readLE8_lt s.mem x.toNat
  · janus64_run [Util.readLE_32, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, Fv256.B.or3_zero_iff, Fv256.B.or2_zero_iff, h3, h2, h1]
    all_goals (refine ⟨?_, ?_⟩)
    all_goals (first | janus_frame | skip)
    · have hX0 := Util.readLE8_lt s.mem x.toNat
      generalize hX : s.mem.readLE x.toNat 8 = X at *
      have hxt : (BitVec.ofNat 64 X).toNat = X := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hX0
      generalize hxv : BitVec.ofNat 64 X = xv at *
      subst hxt
      have hc : IEEEMode (⟨.rne, false, false⟩ : Ctl) := ⟨rfl, rfl⟩
      have hfl := fromInt_lt binary64 .rne
      unfold Fv256.B.float64BitsNearest
      have hmsb : xv.msb = true := by assumption
      have hx : 2 ^ 63 ≤ xv.toNat := by
        rw [BitVec.msb_eq_decide] at hmsb; simp at hmsb; omega
      have hy : (xv >>> 1 ||| BitVec.setWidth 64 (BitVec.setWidth 32 xv &&& 1#32)).toNat =
          xv.toNat / 2 ||| xv.toNat % 2 := by
        rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_and,
          BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow, show (1#32).toNat = 1 from rfl,
          Nat.and_one_is_mod, Nat.pow_one]
        first | (with_reducible congr 1; omega) | (congr 1; omega)
      have hylt : xv.toNat / 2 ||| xv.toNat % 2 < 2 ^ (64 - 1) := by
        have := or_bit (xv.toNat / 2) (xv.toNat % 2) (Nat.mod_lt _ (by decide))
        have hb : xv.toNat / 2 % 2 ||| xv.toNat % 2 < 2 :=
          Nat.or_lt_two_pow (n := 1) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
        omega
      rw [hy, ofInt_ieee hc]
      simp only [hylt, ite_true]
      have h1 : fromInt binary64 .rne ((xv.toNat / 2 ||| xv.toNat % 2 : Nat) : Int) < 18446744073709551616 :=
        hfl _
      rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega : fromInt binary64 .rne
        ((xv.toNat / 2 ||| xv.toNat % 2 : Nat) : Int) < 340282366920938463463374607431768211456)]
      rw [u64_big hc xv.toNat hx xv.isLt]
      have h2 : fromInt binary64 .rne (xv.toNat : Int) < 18446744073709551616 := hfl _
      dsimp only
      omega
    · have hX0 := Util.readLE8_lt s.mem x.toNat
      generalize hX : s.mem.readLE x.toNat 8 = X at *
      have hxt : (BitVec.ofNat 64 X).toNat = X := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hX0
      have hc : IEEEMode (⟨.rne, false, false⟩ : Ctl) := ⟨rfl, rfl⟩
      have hfl := fromInt_lt binary64 .rne
      unfold Fv256.B.float64BitsNearest
      rw [ofInt_ieee hc]
      have hmsb : ¬ (BitVec.ofNat 64 X).msb = true := by assumption
      have hx : X < 2 ^ 63 := by
        rw [BitVec.msb_eq_decide] at hmsb; simp only [hxt] at hmsb; simp at hmsb; omega
      have hlt : fromInt binary64 .rne (X : Int) < 18446744073709551616 := hfl _
      simp only [show X < 2 ^ (64 - 1) from hx, ite_true]
      rw [Nat.mod_eq_of_lt hlt]
      exact Nat.mod_eq_of_lt (by omega)

end Fv256.Amd64.Float64
