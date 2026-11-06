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
  all_goals (trace_state; sorry)

end Fv256.Arm64.RecipSeg
