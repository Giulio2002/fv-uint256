import Fv256.SpecF
import Fv256.MulModMath

/-! `reduce4` summary statement pieces (no proof, cheap to import). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.ReduceSpec

abbrev r4Entry : Nat := 0x4b57c0

abbrev R4Pre (s : State) : Prop :=
  (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
  0x128 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0xb0 ∧ StackWritable s 0x120 0x10 ∧
  Buffer s (s.regs 0) 32 true ∧ Buffer s (s.regs 3) 64 false ∧ Buffer s (s.regs 1) 32 false ∧ Buffer s (s.regs 7) 40 false ∧
  Apart (s.regs 0).toNat 32 ((s.regs 4).toNat - 0x120) 0x130 ∧
  Apart (s.regs 3).toNat 64 ((s.regs 4).toNat - 0x120) 0x130 ∧
  Apart (s.regs 1).toNat 32 ((s.regs 4).toNat - 0x120) 0x130 ∧
  Apart (s.regs 7).toNat 40 ((s.regs 4).toNat - 0x120) 0x130 ∧
  Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 0x120) 0x130 ∧
  s.mem.readLE ((s.regs 1).toNat + 24) 8 ≠ 0 ∧
  Fv256.F.RecipWeak (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 7).toNat 40)

abbrev R4Post (s s' : State) : Prop :=
  s'.regs 0 = s.regs 0 ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
  s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
  s'.mem.readLE (s.regs 0).toNat 32 = s.mem.readLE (s.regs 3).toNat 64 % s.mem.readLE (s.regs 1).toNat 32 ∧
  MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat - 0x120, (s.regs 4).toNat + 0x10)]

theorem hi_lt (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : a * b / 2 ^ 64 < 2 ^ 64 := by
  have h := Nat.mul_lt_mul'' ha hb
  rw [← Nat.pow_add] at h
  exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64)).2 (by rw [← Nat.pow_add]; exact h)

end Fv256.Amd64.ReduceSpec
