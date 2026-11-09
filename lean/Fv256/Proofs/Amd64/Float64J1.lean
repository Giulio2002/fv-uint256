import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.UtilD
import Fv256.Proofs.Common.CodeIn
import Fv256.Proofs.Common.LshProg
import Fv256.Proofs.Amd64.LshSum
import Fv256.Proofs.Amd64.Float64Hc

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float Janus.Amd64.FP

namespace Fv256.Amd64.Float64

set_option maxHeartbeats 4000000 in
theorem lem1 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => (StackGuardOK s 0 ∧ StackWritable s 80 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 80 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧ GoMXCSR s) ∧
        (s.mem.readLE (x.toNat + 16) 8) = 0 ∧ (s.mem.readLE (x.toNat + 24) 8) = 0 ∧ (s.mem.readLE (x.toNat + 8) 8) ≠ 0)
      (fun s s' => (s'.xmm 0).toNat % 2 ^ 64 = Fv256.B.float64BitsNearest (valueAt s x 32) ∧
        MemFrame s.mem s'.mem [((s.regs regSP).toNat - 80, (s.regs regSP).toNat + 8)]) := by
  intro ret hret s hs ⟨⟨hg, ⟨hlow, hnw, hacc⟩, ⟨hxw, hx⟩, hds, hm⟩, ⟨hz2, hz3, hxj⟩⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2
  simp only [regSP] at hacc hlow hnw hds
  simp only [valueAt]
  janus64_run [Util.readLE_32, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, Fv256.B.or3_zero_iff, Fv256.B.or2_zero_iff, hz2, hz3, hxj] calls [hS := Fv256.CodeIn.lib_summary hcLsh (Fv256.Amd64.LshSum.lsh_summary (s.regs 4 - 40#64) x)]
  all_goals clear_states
  all_goals (refine ⟨?_, ?_⟩; rotate_right; janus_frame)
  all_goals clear hS
  all_goals grab_lsh hS3
  all_goals (simp (disch := omega) only [valueAt, Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside] at hS3)
  all_goals have l0 := Util.readLE8_lt s.mem x.toNat
  all_goals have l1 := Util.readLE8_lt s.mem (x.toNat + 8)
  all_goals have l2 := Util.readLE8_lt s.mem (x.toNat + 16)
  all_goals have l3 := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals have hkj : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) < 64 := (Fv256.B.clz_cases _ l1).resolve_left hxj
  all_goals have hbl := Fv256.B.f64_bl1 (s.mem.readLE x.toNat 8) (s.mem.readLE (x.toNat + 8) 8) (Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8)) l0 l1 hxj rfl
  all_goals generalize Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = k at *
  all_goals have m0 := Util.readLE8_lt s'.mem (BitVec.toNat (s.regs 4) - 40)
  all_goals have m1 := Util.readLE8_lt s'.mem (BitVec.toNat (s.regs 4) - 32)
  all_goals have m2 := Util.readLE8_lt s'.mem (BitVec.toNat (s.regs 4) - 24)
  all_goals have m3 := Util.readLE8_lt s'.mem (BitVec.toNat (s.regs 4) - 16)
  all_goals have hsp40 : BitVec.toNat (s.regs 4 - 40#64) = BitVec.toNat (s.regs 4) - 40 := (by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
  all_goals have hexp : (18446744073709551616 - (18446744073709551424 + (63 - k))) = 129 + k := by omega
  all_goals have e8 : BitVec.toNat (s.regs 4) - 40 + 8 = BitVec.toNat (s.regs 4) - 32 := by omega
  all_goals have e16 : BitVec.toNat (s.regs 4) - 40 + 16 = BitVec.toNat (s.regs 4) - 24 := by omega
  all_goals have e24 : BitVec.toNat (s.regs 4) - 40 + 24 = BitVec.toNat (s.regs 4) - 16 := by omega
  all_goals have hS4 := hS3
  all_goals simp only [hexp, hsp40, e8, e16, e24, hz2, hz3, Nat.mul_zero, Nat.add_zero] at hS4
  all_goals first
    | (have hu : ¬ Fv256.D.Up (s'.mem.readLE (BitVec.toNat (s.regs 4) - 40) 8) (s'.mem.readLE (BitVec.toNat (s.regs 4) - 32) 8) (s'.mem.readLE (BitVec.toNat (s.regs 4) - 24) 8) (s'.mem.readLE (BitVec.toNat (s.regs 4) - 16) 8) := by simp only [Fv256.D.Up, Fv256.D.lsb32 _ 11 (by decide), Fv256.D.lsb32 _ 12 (by decide), Fv256.D.ite_tf, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true] at *; omega
       have a1 : (BitVec.ofNat 64 (63 - k + 65)).toNat = 128 - k := (by simp only [BitVec.toNat_ofNat]; omega)
       have a2 : Spec.bitLen (s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8) = 128 - k := (by have h := hbl; simp only [Nat.mul_zero, Nat.add_zero] at h; exact h)
       have a3 : (s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8) < 2 ^ 256 := (by omega)
       have a4 : 2 ^ 64 ≤ (s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8) := (by omega)
       have a5 : (s'.mem.readLE (BitVec.toNat (s.regs 4) - 40) 8) + 2 ^ 64 * (s'.mem.readLE (BitVec.toNat (s.regs 4) - 32) 8) + 2 ^ 128 * (s'.mem.readLE (BitVec.toNat (s.regs 4) - 24) 8) + 2 ^ 192 * (s'.mem.readLE (BitVec.toNat (s.regs 4) - 16) 8) = (s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8) * 2 ^ (257 - (128 - k)) % 2 ^ 256 := (by rw [show 257 - (128 - k) = 129 + k by omega]; exact hS4)
       exact Fv256.D.leafA0 (s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8) (128 - k) _ _ _ _ (BitVec.ofNat 64 (63 - k + 65)) a1 a3 a4 a2 m0 m1 m2 m3 a5 hu)
    | (have hu : Fv256.D.Up (s'.mem.readLE (BitVec.toNat (s.regs 4) - 40) 8) (s'.mem.readLE (BitVec.toNat (s.regs 4) - 32) 8) (s'.mem.readLE (BitVec.toNat (s.regs 4) - 24) 8) (s'.mem.readLE (BitVec.toNat (s.regs 4) - 16) 8) := by simp only [Fv256.D.Up, Fv256.D.lsb32 _ 11 (by decide), Fv256.D.lsb32 _ 12 (by decide), Fv256.D.ite_tf, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true] at *; omega
       have a1 : (BitVec.ofNat 64 (63 - k + 65)).toNat = 128 - k := (by simp only [BitVec.toNat_ofNat]; omega)
       have a2 : Spec.bitLen (s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8) = 128 - k := (by have h := hbl; simp only [Nat.mul_zero, Nat.add_zero] at h; exact h)
       have a3 : (s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8) < 2 ^ 256 := (by omega)
       have a4 : 2 ^ 64 ≤ (s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8) := (by omega)
       have a5 : (s'.mem.readLE (BitVec.toNat (s.regs 4) - 40) 8) + 2 ^ 64 * (s'.mem.readLE (BitVec.toNat (s.regs 4) - 32) 8) + 2 ^ 128 * (s'.mem.readLE (BitVec.toNat (s.regs 4) - 24) 8) + 2 ^ 192 * (s'.mem.readLE (BitVec.toNat (s.regs 4) - 16) 8) = (s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8) * 2 ^ (257 - (128 - k)) % 2 ^ 256 := (by rw [show 257 - (128 - k) = 129 + k by omega]; exact hS4)
       exact Fv256.D.leafA1 (s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8) (128 - k) _ _ _ _ (BitVec.ofNat 64 (63 - k + 65)) a1 a3 a4 a2 m0 m1 m2 m3 a5 hu)

end Fv256.Amd64.Float64
