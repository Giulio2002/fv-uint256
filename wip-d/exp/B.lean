import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.UtilD
import Fv256.Arm64.Float64Lsh

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Float64

set_option profiler true in
set_option profiler.threshold 3000 in
set_option maxHeartbeats 80000000 in
theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => Ptr32 s.mem x false ∧ GuardOK s 0 ∧ StackOK s 88 0 ∧ Disjoint x.toNat 32 (s.sp.toNat - 88) 88 ∧ s.fpcr = 0)
      (fun s s' => s'.getV 0 64 = Fv256.B.float64BitsNearest (val256 s.mem x.toNat) ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 88, s.sp.toNat)]) := by
  intro ret hret s hs ⟨⟨hx, hx'⟩, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hdis, hf⟩
  janus_intro hs
  simp only [Disjoint] at hdis
  janus_run calls [hS := Fv256.Arm64.Float64.lsh_summary (s.sp - 40#64) x]
  all_goals (simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat] at *)
  all_goals (refine ⟨?_, ?_⟩; rotate_right; janus_frame)
  have l0 := Util.readLE8_lt s.mem x.toNat
  have l1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have l2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have l3 := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals first
    | (have hxj : s.mem.readLE (x.toNat + 24) 8 ≠ 0 := ‹¬ s.mem.readLE (x.toNat + 24) 8 = 0›
       have hkj : clzNat 64 s.mem.readLE (x.toNat + 24) 8 < 64 := (Fv256.B.clz_cases _ l3).resolve_left hxj
       have hbl := Fv256.B.f64_bl3 s.mem.readLE x.toNat 8 s.mem.readLE (x.toNat + 8) 8 s.mem.readLE (x.toNat + 16) 8 s.mem.readLE (x.toNat + 24) 8 (clzNat 64 s.mem.readLE (x.toNat + 24) 8) l0 l1 l2 l3 hxj rfl
       have hS3 := ‹val256 s'.mem _ = Spec.lsh _ _›
       generalize clzNat 64 s.mem.readLE (x.toNat + 24) 8 = k at *
       have m0 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 40)
       have m1 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 32)
       have m2 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 24)
       have m3 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 16)
       have hsp40 : (s.sp - 40#64).toNat = s.sp.toNat - 40 := by rw [BitVec.toNat_sub]; simp; omega
       have hsh : (257#64 - (64#64 - BitVec.ofNat 64 k + 192#64)).toNat = 1 + k := by
         rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_add]; simp; omega
       simp (disch := omega) only [val256, Spec.lsh, Spec.W, setReg_apply, hsp40, hsh, Janus.Arm64.Memory.readLE_writeLE_of_disjoint] at hS3
       simp only [lsb_ofNat _ 11 (by decide), lsb0_toNat, fr_toNat _ m3, Nat.or_eq_zero_iff] at *
       sorry)
    | (have hxj : s.mem.readLE (x.toNat + 16) 8 ≠ 0 := ‹¬ s.mem.readLE (x.toNat + 16) 8 = 0›
       have hz3 : s.mem.readLE (x.toNat + 24) 8 = 0 := ‹s.mem.readLE (x.toNat + 24) 8 = 0›
       have hkj : clzNat 64 s.mem.readLE (x.toNat + 16) 8 < 64 := (Fv256.B.clz_cases _ l2).resolve_left hxj
       have hbl := Fv256.B.f64_bl2 s.mem.readLE x.toNat 8 s.mem.readLE (x.toNat + 8) 8 s.mem.readLE (x.toNat + 16) 8 (clzNat 64 s.mem.readLE (x.toNat + 16) 8) l0 l1 l2 hxj rfl
       have hS3 := ‹val256 s'.mem _ = Spec.lsh _ _›
       generalize clzNat 64 s.mem.readLE (x.toNat + 16) 8 = k at *
       have m0 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 40)
       have m1 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 32)
       have m2 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 24)
       have m3 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 16)
       have hsp40 : (s.sp - 40#64).toNat = s.sp.toNat - 40 := by rw [BitVec.toNat_sub]; simp; omega
       have hsh : (257#64 - (64#64 - BitVec.ofNat 64 k + 128#64)).toNat = 65 + k := by
         rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_add]; simp; omega
       simp (disch := omega) only [val256, Spec.lsh, Spec.W, setReg_apply, hsp40, hsh, Janus.Arm64.Memory.readLE_writeLE_of_disjoint] at hS3
       simp only [lsb_ofNat _ 11 (by decide), lsb0_toNat, fr_toNat _ m3, Nat.or_eq_zero_iff] at *
       sorry)
    | (have hxj : s.mem.readLE (x.toNat + 8) 8 ≠ 0 := ‹¬ s.mem.readLE (x.toNat + 8) 8 = 0›
       have hz2 : s.mem.readLE (x.toNat + 16) 8 = 0 := ‹s.mem.readLE (x.toNat + 16) 8 = 0›
       have hz3 : s.mem.readLE (x.toNat + 24) 8 = 0 := ‹s.mem.readLE (x.toNat + 24) 8 = 0›
       have hkj : clzNat 64 s.mem.readLE (x.toNat + 8) 8 < 64 := (Fv256.B.clz_cases _ l1).resolve_left hxj
       have hbl := Fv256.B.f64_bl1 s.mem.readLE x.toNat 8 s.mem.readLE (x.toNat + 8) 8 (clzNat 64 s.mem.readLE (x.toNat + 8) 8) l0 l1 hxj rfl
       have hS3 := ‹val256 s'.mem _ = Spec.lsh _ _›
       generalize clzNat 64 s.mem.readLE (x.toNat + 8) 8 = k at *
       have m0 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 40)
       have m1 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 32)
       have m2 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 24)
       have m3 := Util.readLE8_lt s'.mem (BitVec.toNat s.sp - 16)
       have hsp40 : (s.sp - 40#64).toNat = s.sp.toNat - 40 := by rw [BitVec.toNat_sub]; simp; omega
       have hsh : (257#64 - (64#64 - BitVec.ofNat 64 k + 64#64)).toNat = 129 + k := by
         rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_add]; simp; omega
       simp (disch := omega) only [val256, Spec.lsh, Spec.W, setReg_apply, hsp40, hsh, Janus.Arm64.Memory.readLE_writeLE_of_disjoint] at hS3
       simp only [lsb_ofNat _ 11 (by decide), lsb0_toNat, fr_toNat _ m3, Nat.or_eq_zero_iff] at *
       sorry)
    | sorry

end Fv256.Arm64.Float64
