import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC

/-!
# `(*uint256.Int).SetFromBig(b *big.Int) bool` (amd64)

`big.Int` is `{neg bool; abs nat}` with `nat = []Word`: `neg` at offset 0, the word array pointer at 8, its length at 16.
The Go ABI returns the bool in `AL` only, so the statement is about the low byte of `RAX`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SetFromBig

theorem correctness (z b pw len : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, b]
      (fun s => StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s b 32 false ∧ s.mem.readLE b.toNat 1 < 2 ∧
        s.mem.readLE (b.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (b.toNat + 16) 8 = len.toNat ∧
        Buffer s pw (8 * len.toNat) false ∧
        Disjoint z 32 b 32 ∧ Disjoint z 32 pw (8 * len.toNat) ∧ Disjoint z 32 (s.regs regSP) 8)
      (fun s s' => (s'.regs 0).toNat % 256 = (if Fv256.C.fromBigOv len.toNat then 1 else 0) ∧
        valueAt s' z 32 =
          Fv256.C.fromBig (s.mem.readLE b.toNat 1 == 1)
            (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
        Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨_, hnw, hacc⟩, ⟨hz', hz⟩, ⟨hb', hb⟩, hneg, hpw, hlen, ⟨hw', hw⟩, hd1, hd2, hds⟩
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw hds
  simp only [valueAt, Disjoint] at *
  janus64_run [Util.readLE_32]
  all_goals (refine ⟨?_, ?_⟩)
  all_goals (try (first | exact (Fv256.C.ov8 _) | (rw [show (Fv256.C.fromBigOv 0).toNat = 0 from rfl]; exact Fv256.C.lowbyte0 z)))
  all_goals (
    simp only [hlen, hpw] at *
    have hl64 := len.isLt
    have l0 := Util.readLE8_lt s.mem pw.toNat
    have l1 := Util.readLE8_lt s.mem (pw.toNat + 8)
    have l2 := Util.readLE8_lt s.mem (pw.toNat + 16)
    have l3 := Util.readLE8_lt s.mem (pw.toNat + 24)
    have hn : s.mem.readLE b.toNat 1 = 0 ∨ s.mem.readLE b.toNat 1 = 1 := by omega
    have hc : len.toNat = 0 ∨ len.toNat = 1 ∨ len.toNat = 2 ∨ len.toNat = 3 ∨ len.toNat = 4 ∨ 5 ≤ len.toNat := by omega
    rcases hn with hn | hn <;> rcases hc with h | h | h | h | h | h
    all_goals first
      | (exfalso; omega)
      | (exfalso; simp at hbr; done)
      | (simp only [Fv256.C.fromBig, Fv256.C.fromBigOv, Spec.neg, Spec.W]
         first
           | (rw [Fv256.C.bigAbs_mod _ _ (by omega : 4 ≤ len.toNat)]; simp only [h, hn, Fv256.C.bigAbs]; try simp)
           | (simp only [h, hn, Fv256.C.bigAbs]; try simp)))
  all_goals (try simp only [Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Spec.neg, Spec.W])
  all_goals (try simp only [Nat.cast_ofNat, Int.reduceLE, ↓reduceIte, decide_eq_true_eq, Nat.reduceLT, decide_false, Bool.false_eq_true, ite_false, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Fv256.C.fromBigOv])
  all_goals ((try generalize s.mem.readLE pw.toNat 8 = x0 at *); (try generalize s.mem.readLE (pw.toNat + 8) 8 = x1 at *); (try generalize s.mem.readLE (pw.toNat + 16) 8 = x2 at *); (try generalize s.mem.readLE (pw.toNat + 24) 8 = x3 at *); first | (janus_decide_split <;> omega) | omega | (trace_state; fail "y"))
  all_goals fail "x"

end Fv256.Amd64.SetFromBig
