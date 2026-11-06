import Fv256.Arm64.RecipLive
import Fv256.Arm64.RecipNat

/-!
# `Reciprocal` (arm64), segment 0: entry .. `recEntry + 0x88` (prologue, power-of-two test, inline `Lsh` call)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.RecipSeg
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- the `i`-th limb of `m` (the input at `X0`) -/
def mw (s : State) (i : Nat) : Nat := s.mem.readLE ((s.regs 0).toNat + 8 * i) 8

/-- the value `m` -/
def mval (s : State) : Nat := mw s 0 + 2 ^ 64 * mw s 1 + 2 ^ 128 * mw s 2 + 2 ^ 192 * mw s 3

/-- state at `recEntry + 0x88`: `y = m << clz(m3)` in the local words `sp+32 .. sp+63`, the shift index in `sp+176` -/
def Q0 (s S' : State) : Prop := ∃ y0 y1 y2 y3 sidx : Nat,
  L88 S' y0 y1 y2 y3 sidx ∧
  y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 = Fv256.Spec.lsh (mval s) (clzNat 64 (mw s 3)) ∧
  sidx = 255 - clzNat 64 (mw s 3) ∧ 2 ^ 63 ≤ y3 ∧ RecRegs s S' ∧ RecMem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem seg0 (s : State) (hpc : s.pc = BitVec.ofNat 64 recEntry) (hpre : RecPre s)
    (hm3 : s.mem.readLE ((s.regs 0).toNat + 24) 8 ≠ 0)
    (hz : ¬ (s.mem.readLE ((s.regs 0).toNat + 24) 8 &&& s.mem.readLE ((s.regs 0).toNat + 24) 8 - 1 |||
      (s.mem.readLE ((s.regs 0).toNat + 16) 8 ||| (s.mem.readLE ((s.regs 0).toNat + 8) 8 ||| s.mem.readLE (s.regs 0).toNat 8))) = 0) :
    ReachesRet Fv256.Arm64.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x88)) s (Q0 s) := by
  have hpre' := hpre
  obtain ⟨h1, h2, ⟨hg1, hg2, hg3⟩, ⟨hsa, hsb, hsc, hsd⟩, hgw, hm1, hm2, hmd⟩ := hpre
  have hclz : Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) ≤ 63 :=
    Fv256.Arm64.RecipNat.clz_le _ (Util.readLE8_lt _ _) hm3
  janus_run until [recEntry + 0x88]
  all_goals (
  refine Janus.Tactic.ReachesRet.done (by first | rfl | decide | simp [recEntry, segAddr]) ?_
  have b0 := Util.readLE8_lt s.mem (s.regs 0).toNat
  have b1 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)
  have b2 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 16)
  have b3 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 24)
  have hspe : (s.sp - 272#64).toNat = s.sp.toNat - 272 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  unfold Q0 mval mw
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, show 8 * 2 = 16 from rfl, show 8 * 3 = 24 from rfl]
  generalize hn : clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) = n at *
  generalize hm0 : s.mem.readLE (s.regs 0).toNat 8 = m0 at *
  generalize hm1 : s.mem.readLE ((s.regs 0).toNat + 8) 8 = m1 at *
  generalize hm2 : s.mem.readLE ((s.regs 0).toNat + 16) 8 = m2 at *
  generalize hm3' : s.mem.readLE ((s.regs 0).toNat + 24) 8 = m3 at *
  have hn63 : n ≤ 63 := hclz
  have hlsh : m0 * 2 ^ n % 2 ^ 64 + 2 ^ 64 * (m1 * 2 ^ n % 2 ^ 64 + m0 / 2 ^ (64 - n)) +
      2 ^ 128 * (m2 * 2 ^ n % 2 ^ 64 + m1 / 2 ^ (64 - n)) + 2 ^ 192 * (m3 * 2 ^ n % 2 ^ 64 + m2 / 2 ^ (64 - n)) =
      Fv256.Spec.lsh (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3) n := by
    have := Util.lsh0_t m0 m1 m2 m3 n (by omega) b0 b1 b2 b3
    unfold Fv256.Spec.lsh Fv256.Spec.W
    simpa only [Nat.reducePow] using this
  have lt0 : m0 * 2 ^ n % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have lt1 := Fv256.Arm64.RecipNat.word_lt m0 m1 n b0 hn63
  have lt2 := Fv256.Arm64.RecipNat.word_lt m1 m2 n b1 hn63
  have lt3 := Fv256.Arm64.RecipNat.word_lt m2 m3 n b2 hn63
  have hy3 : 2 ^ 63 ≤ m3 * 2 ^ n % 2 ^ 64 + m2 / 2 ^ (64 - n) :=
    Fv256.Arm64.RecipNat.top_ge m0 m1 m2 m3 n b0 b1 b2 b3 hm3 hn.symm _ _ _ _ lt0 lt1 lt2 lt3 hlsh
  refine ⟨m0 * 2 ^ n % 2 ^ 64, m1 * 2 ^ n % 2 ^ 64 + m0 / 2 ^ (64 - n), m2 * 2 ^ n % 2 ^ 64 + m1 / 2 ^ (64 - n),
    m3 * 2 ^ n % 2 ^ 64 + m2 / 2 ^ (64 - n), 255 - n, ?_, hlsh, rfl, hy3, ?_, ?_⟩
  · unfold L88
    have slot : ∀ d : Nat, ∀ a v : Nat, a = s.sp.toNat - 272 + d → s.sp.toNat - 280 ≤ a → True := fun _ _ _ _ _ => trivial
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · dsimp only; rw [hspe, show s.sp.toNat - 272 + 32 = s.sp.toNat - 240 by omega]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first
        | (have h0 : n = 0 := (by omega)
           subst h0
           simp [Nat.mod_eq_of_lt b0])
        | (have hpos : 1 ≤ n := (by omega)
           rw [Nat.mod_eq_of_lt (show n < 64 by omega), show (256:Nat) ^ 8 = 2 ^ 64 from rfl])
    · dsimp only; rw [hspe, show s.sp.toNat - 272 + 40 = s.sp.toNat - 232 by omega]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first
        | (have h0 : n = 0 := (by omega)
           subst h0
           simp [Nat.mod_eq_of_lt b1, Nat.div_eq_of_lt b0])
        | (have hpos : 1 ≤ n := (by omega)
           rw [Nat.mod_eq_of_lt (show n < 64 by omega), Fv256.Arm64.RecipNat.word_or m0 m1 n b0 b1 hpos hn63, show (256:Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt lt1])
    · dsimp only; rw [hspe, show s.sp.toNat - 272 + 48 = s.sp.toNat - 224 by omega]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first
        | (have h0 : n = 0 := (by omega)
           subst h0
           simp [Nat.mod_eq_of_lt b2, Nat.div_eq_of_lt b1])
        | (have hpos : 1 ≤ n := (by omega)
           rw [Nat.mod_eq_of_lt (show n < 64 by omega), Fv256.Arm64.RecipNat.word_or m1 m2 n b1 b2 hpos hn63, show (256:Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt lt2])
    · dsimp only; rw [hspe, show s.sp.toNat - 272 + 56 = s.sp.toNat - 216 by omega]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first
        | (have h0 : n = 0 := (by omega)
           subst h0
           simp [Nat.mod_eq_of_lt b3, Nat.div_eq_of_lt b2])
        | (have hpos : 1 ≤ n := (by omega)
           rw [Nat.mod_eq_of_lt (show n < 64 by omega), Fv256.Arm64.RecipNat.word_or m2 m3 n b2 b3 hpos hn63, show (256:Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt lt3])
    · dsimp only; rw [hspe, show s.sp.toNat - 272 + 176 = s.sp.toNat - 96 by omega]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first
        | (have h0 : n = 0 := (by omega)
           subst h0
           simp)
        | (have hpos : 1 ≤ n := (by omega)
           rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; omega)
  · refine ⟨rfl, ?_, ?_⟩ <;> simp [setReg]
  · refine ⟨?_, ?_, ?_⟩
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (BitVec.isLt _)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (BitVec.isLt _)
    · repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (r := (s.sp.toNat - 280, s.sp.toNat + 48)) (by simp) (by omega) (by omega))

end Fv256.Arm64.RecipSeg
