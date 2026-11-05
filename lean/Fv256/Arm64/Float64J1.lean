import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.UtilD
import Fv256.Arm64.Float64Lsh

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Float64

set_option maxHeartbeats 8000000 in
theorem lem1 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => (Ptr32 s.mem x false ∧ GuardOK s 0 ∧ StackOK s 88 0 ∧ Disjoint x.toNat 32 (s.sp.toNat - 88) 88 ∧ s.fpcr = 0) ∧ ((s.mem.readLE (x.toNat + 16) 8) = 0 ∧ (s.mem.readLE (x.toNat + 24) 8) = 0 ∧ (s.mem.readLE (x.toNat + 8) 8) ≠ 0))
      (fun s s' => s'.getV 0 64 = Fv256.B.float64BitsNearest (val256 s.mem x.toNat) ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 88, s.sp.toNat)]) := by
  intro ret hret s hs ⟨⟨⟨hx, hx'⟩, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hdis, hf⟩, ⟨hz2, hz3, hxj⟩⟩
  janus_intro hs
  simp only [Disjoint] at hdis
  janus_run calls [hS := Fv256.Arm64.Float64.lsh_summary (s.sp - 40#64) x]
  all_goals clear_states
  all_goals (simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat] at *)
  all_goals (refine ⟨?_, ?_⟩; rotate_right; janus_frame)
  all_goals have l0 := Util.readLE8_lt s.mem x.toNat
  all_goals have l1 := Util.readLE8_lt s.mem (x.toNat + 8)
  all_goals have l2 := Util.readLE8_lt s.mem (x.toNat + 16)
  all_goals have l3 := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals have hkj : clzNat 64 (s.mem.readLE (x.toNat + 8) 8) < 64 := (Fv256.B.clz_cases _ l1).resolve_left hxj
  all_goals have hbl := Fv256.B.f64_bl1 (s.mem.readLE x.toNat 8) (s.mem.readLE (x.toNat + 8) 8) (clzNat 64 (s.mem.readLE (x.toNat + 8) 8)) l0 l1 hxj rfl
  all_goals grab_lsh hS3
  all_goals generalize clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = k at *
  all_goals have m0 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 40)
  all_goals have m1 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 32)
  all_goals have m2 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 24)
  all_goals have m3 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 16)
  all_goals have hexp : (18446744073709551616 - (18446744073709551616 - k % 18446744073709551616 + 64 + 64) % 18446744073709551616 + 257) % 18446744073709551616 = 129 + k := by omega
  all_goals have e8 : BitVec.toNat s.sp - 40 + 8 = BitVec.toNat s.sp - 32 := by omega
  all_goals have e16 : BitVec.toNat s.sp - 40 + 16 = BitVec.toNat s.sp - 24 := by omega
  all_goals have e24 : BitVec.toNat s.sp - 40 + 24 = BitVec.toNat s.sp - 16 := by omega
  all_goals have hS4 := hS3
  all_goals simp only [hexp, e8, e16, e24, hz2, hz3, Nat.mul_zero, Nat.add_zero] at hS4
  all_goals first
    | (refine Fv256.D.leaf0 _ (128 - k) _ _ _ _ _ (by simp only [BitVec.toNat_ofNat]; omega) (by omega) (by omega) (by simpa using hbl) m0 m1 m2 m3 (by rw [show 257 - (128 - k) = 129 + k by omega]; exact hS4) (by simp only [Fv256.D.Up, Fv256.D.lsb_ofNat _ 11 (by decide), Fv256.D.fr_toNat _ m3, Nat.or_eq_zero_iff, beq_iff_eq, beq_eq_false_iff_ne, Bool.not_eq_true, decide_eq_true_eq, decide_eq_false_iff_not] at *; omega))
    | (refine Fv256.D.leaf1 _ (128 - k) _ _ _ _ _ (by simp only [BitVec.toNat_ofNat]; omega) (by omega) (by omega) (by simpa using hbl) m0 m1 m2 m3 (by rw [show 257 - (128 - k) = 129 + k by omega]; exact hS4) (by simp only [Fv256.D.Up, Fv256.D.lsb_ofNat _ 11 (by decide), Fv256.D.fr_toNat _ m3, Nat.or_eq_zero_iff, beq_iff_eq, beq_eq_false_iff_ne, Bool.not_eq_true, decide_eq_true_eq, decide_eq_false_iff_not] at *; omega))

end Fv256.Arm64.Float64
