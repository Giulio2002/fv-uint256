import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.SumC

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.FromBigSfb

set_option maxHeartbeats 8000000 in
theorem sfb_summary (impl : List Segment) (pw len : BitVec 64) :
    Fv256.C.SfbSummary (Extracted.program.link impl) (segAddr Extracted.program "github.com/holiman/uint256.(*Int).SetFromBig") pw len := by
  intro s hpc ⟨h30a, h30b, ⟨hz, hz'⟩, ⟨⟨hb, hb'⟩, hneg, hpw, hlen, ⟨hw, hw'⟩⟩, hd1, hd2⟩
  simp only [Disjoint] at hd1 hd2
  janus_run
  all_goals (
    simp only [hlen, hpw] at *
    have hl64 := len.isLt
    have l0 := Util.readLE8_lt s.mem pw.toNat
    have l1 := Util.readLE8_lt s.mem (pw.toNat + 8)
    have l2 := Util.readLE8_lt s.mem (pw.toNat + 16)
    have l3 := Util.readLE8_lt s.mem (pw.toNat + 24)
    have hn : s.mem.readLE (s.regs 1).toNat 1 = 0 ∨ s.mem.readLE (s.regs 1).toNat 1 = 1 := by omega
    have hc : len.toNat = 0 ∨ len.toNat = 1 ∨ len.toNat = 2 ∨ len.toNat = 3 ∨ len.toNat = 4 ∨ 5 ≤ len.toNat := by omega
    have e0 : (addWithCarry (0#64) (1#64) false).snd.z = false := by decide
    have e1 : (addWithCarry (18446744073709551615#64) (1#64) false).snd.z = true := by decide
    have e2 : (addWithCarry (1#64) (1#64) false).snd.z = false := by decide
    simp only [e0, e1, e2] at *
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
  all_goals (try (first | refine ⟨Fv256.C.ov_flag _, ?_⟩ | refine ⟨Fv256.C.ov_flag' _, ?_⟩))
  all_goals (try (refine And.intro ?_ ?_; rotate_left; janus_frame; rotate_left))
  all_goals (try janus_frame)
  all_goals ((try generalize s.mem.readLE pw.toNat 8 = x0 at *); (try generalize s.mem.readLE (pw.toNat + 8) 8 = x1 at *); (try generalize s.mem.readLE (pw.toNat + 16) 8 = x2 at *); (try generalize s.mem.readLE (pw.toNat + 24) 8 = x3 at *); first | (janus_decide_split <;> omega) | omega | (trace_state; fail "y"))
  all_goals (trace_state; fail "x")


end Fv256.Arm64.FromBigSfb
