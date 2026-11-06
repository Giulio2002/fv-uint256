import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecF
import Fv256.SqrtMath
import Fv256.SqrtHead
import Fv256.SpecB
import Fv256.UtilB

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Sqrt

abbrev headS : Nat := Extracted.entry + 0x312

theorem headS_lt : headS + 0x100 < 2 ^ 47 := by decide

/-- state at the head of the uint64 loop: `z1` in `RBX`, `x0` in `RDX`, receiver in `RAX` -/
def SmallInv (s0 : State) (x0 z1 : Nat) (z : BitVec 64) (S : State) : Prop :=
  S.rip = BitVec.ofNat 64 headS ∧ S.regs 3 = BitVec.ofNat 64 z1 ∧ S.regs 2 = BitVec.ofNat 64 x0 ∧ S.regs 0 = z ∧
  S.regs 4 = s0.regs 4 - 136#64 ∧ S.regs 5 = s0.regs 4 - 8#64 ∧ S.regs 14 = s0.regs 14 ∧ S.xmm 15 = 0 ∧
  S.df = s0.df ∧ S.mxcsr = s0.mxcsr ∧
  0 < z1 ∧ z1 ≤ 2 ^ 32 ∧ 2 ≤ x0 ∧ x0 < 2 ^ 64 ∧ x0 < (z1 + 1) * (z1 + 1) ∧
  S.mem.accessible z.toNat 32 true = true ∧ z.toNat + 32 ≤ 2 ^ 48 ∧
  S.mem.accessible ((s0.regs 4).toNat - 8) 16 false = true ∧
  S.mem.readLE ((s0.regs 4).toNat - 8) 8 = (s0.regs 5).toNat ∧
  (z.toNat + 32 ≤ (s0.regs 4).toNat - 8 ∨ (s0.regs 4).toNat + 8 ≤ z.toNat) ∧
  MemFrame s0.mem S.mem [((s0.regs 4).toNat - 8, (s0.regs 4).toNat)]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
theorem small_loop (s0 : State) (x0 : Nat) (z : BitVec 64) (Q : State → Prop) (hsp : 0x280 ≤ (s0.regs 4).toNat)
    (hsp48 : (s0.regs 4).toNat + 8 ≤ 2 ^ 48)
    (hret47 : s0.mem.readLE (s0.regs 4).toNat 8 < 2 ^ 47) :
    ∀ z1 (S : State), SmallInv s0 x0 z1 z S →
      (∀ r (S' : State), SqrtMath.IsSqrt x0 r →
        S'.regs 0 = z → S'.regs 4 = s0.regs 4 + 8#64 → S'.regs 5 = s0.regs 5 → S'.regs 14 = s0.regs 14 → S'.xmm 15 = 0 →
        S'.df = s0.df → S'.mxcsr = s0.mxcsr → S'.mem.readLE z.toNat 32 = r →
        MemFrame s0.mem S'.mem [(z.toNat, z.toNat + 32), ((s0.regs 4).toNat - 8, (s0.regs 4).toNat)] → Q S') →
      ReachesRet Extracted.program (retAddrOf s0) S Q := by
  intro z1
  induction z1 using Nat.strongRecOn with
  | _ z1 ih =>
    intro S hI hex
    obtain ⟨hpc, r3, r2, r0, r4, r5, r14, x15, hdf, hmx, hz1, hz1le, hx2, hx64, hinv, hza, hzw, hsa, hsv, hdz, hfr⟩ := hI
    have hcode := headS_lt
    have hq := Nat.div_le_self x0 z1
    have esp8 : (18446744073709551608 + BitVec.toNat (s0.regs 4)) % 18446744073709551616 = (s0.regs 4).toNat - 8 := by omega
    have hsum := SqrtMath.no_overflow_64 x0 z1 hz1 hz1le hinv
    have hqle : x0 / z1 < 2 ^ 64 := by omega
    have hz2' : (BitVec.ofNat 64 z1 + BitVec.ofNat 64 (x0 / z1)) >>> 1 = BitVec.ofNat 64 ((z1 + x0 / z1) / 2) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      have e1 : z1 % 2 ^ 64 = z1 := Nat.mod_eq_of_lt (by omega)
      have e2 : x0 / z1 % 2 ^ 64 = x0 / z1 := Nat.mod_eq_of_lt hqle
      have e3 : (z1 + x0 / z1) % 2 ^ 64 = z1 + x0 / z1 := Nat.mod_eq_of_lt hsum
      have e4 : (z1 + x0 / z1) / 2 % 2 ^ 64 = (z1 + x0 / z1) / 2 := Nat.mod_eq_of_lt (by omega)
      rw [e1, e2, e3, e4]
    have hz2 : ((BitVec.ofNat 64 z1 + BitVec.ofNat 64 (x0 / z1)) >>> 1).toNat = (z1 + x0 / z1) / 2 := by
      rw [hz2', BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    janus64_run [r3, r2, r0, r4, r5, r14, x15, hdf, hmx, esp8] until [headS]
    · rename_i hb0 hb1
      have hlt : (z1 + x0 / z1) / 2 < z1 := by
        rw [hz2] at hbr; omega
      have hinv' := SqrtMath.inv_step x0 z1 hz1 hinv
      have hpos := SqrtMath.step_pos x0 z1 hz1 (by omega) hinv
      unfold SqrtMath.step at hinv' hpos
      refine ih ((z1 + x0 / z1) / 2) hlt _ ?_ hex
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hpos, by omega, hx2, hx64, hinv', hza, hzw, hsa, hsv, hdz, hfr⟩
      · simp [setRegF, headS, Extracted.entry]
      · simp [setRegF]; exact hz2'
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF, r4]
      · simp [setRegF, r5]
      · simp [setRegF, r14]
      · simp [setRegF, x15]
      · simp
      · simp
    · rename_i hb0 hb1 hb2
      have hstop : z1 ≤ SqrtMath.step x0 z1 := by
        unfold SqrtMath.step; rw [hz2] at hb2; omega
      have hsq := SqrtMath.isSqrt_of_stop x0 z1 hz1 hinv hstop
      refine hex z1 _ hsq ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · simp [setRegF]
      · simp [setRegF, r4]
      · simp [setRegF, r5]
      · simp [setRegF, r14]
      · simp [setRegF, x15]
      · simp
      · simp
      · simp (disch := omega) only [Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]
        have hz1l : z1 < 256 ^ 8 := by
          have : (2 : Nat) ^ 32 < 256 ^ 8 := by decide
          omega
        rw [Nat.mod_eq_of_lt hz1l]
        simp
      · janus_frame

end Fv256.Amd64.Sqrt
