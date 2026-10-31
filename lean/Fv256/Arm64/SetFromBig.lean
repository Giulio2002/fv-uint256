import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC

/-!
# `(*uint256.Int).SetFromBig(b *big.Int) bool` (arm64)

`big.Int` is `{neg bool; abs nat}` with `nat = []Word`: `neg` at offset 0, the word array pointer at 8, its length at 16.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SetFromBig

theorem correctness (z b pw len : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, b]
      (fun s => Ptr32 s.mem z true ∧ Ptr s.mem b 32 false ∧ s.mem.readLE b.toNat 1 < 2 ∧
        s.mem.readLE (b.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (b.toNat + 16) 8 = len.toNat ∧
        Ptr s.mem pw (8 * len.toNat) false ∧
        Disjoint z.toNat 32 b.toNat 32 ∧ Disjoint z.toNat 32 pw.toNat (8 * len.toNat))
      (fun s s' => (s'.regs 0).toNat = (if Fv256.C.fromBigOv len.toNat then 1 else 0) ∧
        val256 s'.mem z.toNat =
          Fv256.C.fromBig (s.mem.readLE b.toNat 1 == 1)
            (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
        OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hb, hb'⟩, hneg, hpw, hlen, ⟨hw, hw'⟩, hd1, hd2⟩
  janus_intro hs
  simp only [Disjoint] at hd1 hd2
  janus_run
  all_goals (
    simp only [hlen, hpw] at *
    have hl64 := len.isLt
    have l0 := Util.readLE8_lt s.mem pw.toNat
    have l1 := Util.readLE8_lt s.mem (pw.toNat + 8)
    have l2 := Util.readLE8_lt s.mem (pw.toNat + 16)
    have l3 := Util.readLE8_lt s.mem (pw.toNat + 24)
    have hn : s.mem.readLE b.toNat 1 = 0 ∨ s.mem.readLE b.toNat 1 = 1 := by omega
    have hc : len.toNat = 0 ∨ len.toNat = 1 ∨ len.toNat = 2 ∨ len.toNat = 3 ∨ len.toNat = 4 ∨ 5 ≤ len.toNat := by omega
    have e0 : (addWithCarry (0#64) (1#64) false).snd.z = false := by decide
    have e1 : (addWithCarry (18446744073709551615#64) (1#64) false).snd.z = true := by decide
    simp only [e0, e1] at *
    rcases hn with hn | hn <;> rcases hc with h | h | h | h | h | h
    all_goals first
      | (exfalso; omega)
      | (simp only [Fv256.C.fromBig, Fv256.C.fromBigOv, Spec.neg, Spec.W]
         first
           | (rw [Fv256.C.bigAbs_mod _ _ (by omega : 4 ≤ len.toNat)]; simp only [h, hn, Fv256.C.bigAbs])
           | (simp only [h, hn, Fv256.C.bigAbs]; try simp)))
  all_goals (try (simp only [Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Spec.neg, Spec.W]; janus_decide_split <;> omega))
  all_goals (trace_state; fail "x")

end Fv256.Arm64.SetFromBig
