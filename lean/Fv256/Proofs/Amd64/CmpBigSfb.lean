import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.SpecC
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.UtilC
import Fv256.Proofs.Common.SumC64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.CmpBigSfb

set_option maxHeartbeats 8000000 in
theorem sfb_summary (z b pw len : BitVec 64) :
    Fv256.C.SfbSummary64 Extracted.program (segAddr Extracted.program "github.com/holiman/uint256.(*Int).SetFromBig") z b pw len := by
  intro s hpc ⟨⟨hr1, hr2, hx15, hdf⟩, hz0, hb0, ⟨hz', hz⟩, ⟨hb', hb⟩, hneg, hpw, hlen, ⟨hw', hw⟩, hd1, hd2, hds⟩
  simp only [valueAt, Disjoint] at *
  janus64_run [Util.readLE_32]
  all_goals
    refine And.intro ?_ (And.intro ?_ ?_)
    · first | exact Fv256.C.ov8 _ | (rw [show (Fv256.C.fromBigOv 0).toNat = 0 from rfl]; exact Fv256.C.lowbyte0 z)
    · simp only [hlen, hpw] at *
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
        | (exfalso; simp [hn] at hbr; done)
        | (exfalso; have hq := ‹¬BitVec.ofNat 8 (Janus.Arm64.Memory.readLE s.mem b.toNat 1) = 0#8›; rw [hn] at hq; exact hq (by decide))
        | (exfalso; have hq := ‹BitVec.ofNat 8 (Janus.Arm64.Memory.readLE s.mem b.toNat 1) = 0#8›; rw [hn] at hq; exact absurd hq (by decide))
        | (simp only [Fv256.C.fromBig, Fv256.C.fromBigOv, Spec.neg, Spec.W]
           first
             | (rw [Fv256.C.bigAbs_mod _ _ (by omega : 4 ≤ len.toNat)]; simp only [h, hn, Fv256.C.bigAbs]; try simp)
             | (simp only [h, hn, Fv256.C.bigAbs]; try simp))
      all_goals (try simp only [Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Spec.neg, Spec.W])
      all_goals (try simp only [Nat.cast_ofNat, Int.reduceLE, ↓reduceIte, decide_eq_true_eq, Nat.reduceLT, decide_false, Bool.false_eq_true, ite_false, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Fv256.C.fromBigOv])
      all_goals (try simp only [Fv256.C.ite_sub])
      all_goals ((try generalize s.mem.readLE pw.toNat 8 = x0 at *); (try generalize s.mem.readLE (pw.toNat + 8) 8 = x1 at *); (try generalize s.mem.readLE (pw.toNat + 16) 8 = x2 at *); (try generalize s.mem.readLE (pw.toNat + 24) 8 = x3 at *); first | (have key := Util.neg_chain x0 x1 x2 x3 l0 l1 l2 l3; have e : (x0 + x1 * 18446744073709551616 + x2 * 340282366920938463463374607431768211456 + x3 * 6277101735386680763835789423207666416102355444464034512896) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = (x0 + x1 * 18446744073709551616 + x2 * 340282366920938463463374607431768211456 + x3 * 6277101735386680763835789423207666416102355444464034512896) := Nat.mod_eq_of_lt (by omega); rw [e]; omega) | (have key := Util.neg_chain x0 0 0 0 l0 (by decide) (by decide) (by decide); simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at key; omega) | (have key := Util.neg_chain x0 x1 0 0 l0 l1 (by decide) (by decide); simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at key; omega) | (have key := Util.neg_chain x0 x1 x2 0 l0 l1 l2 (by decide); simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at key; omega) | (have key := Util.neg_chain x0 x1 x2 x3 l0 l1 l2 l3; simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at key; omega) | (janus_decide_split <;> omega) | omega | (trace_state; fail "y"))
    · janus_frame

end Fv256.Amd64.CmpBigSfb
