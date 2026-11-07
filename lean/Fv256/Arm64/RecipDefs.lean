import Fv256.Spec
import Fv256.Util
import Fv256.UtilB
import Fv256.Arm64.RecipBv
import Fv256.RecipSpec
import Fv256.Arm64.SegCompose
import Fv256.Arm64.RecipProg

/-!
# `Reciprocal` (arm64): entry precondition, frame invariants shared by all segment lemmas
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.RecipSeg

abbrev recEntry : Nat := segAddr Fv256.Arm64.RecipProg.program "github.com/holiman/uint256.Reciprocal"

/-- `Reciprocal(m)` called with `m` in `X0`; the 5-word result is written to the caller frame at `sp+8 .. sp+48` -/
def RecPre (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 0x90 ∧ StackOK s 0x118 0x30 ∧
  ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 0x118 ∨ s.sp.toNat + 0x30 ≤ (s.regs 28).toNat + 16) ∧
  (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 false = true ∧
  ((s.regs 0).toNat + 32 ≤ s.sp.toNat - 0x118 ∨ s.sp.toNat + 0x30 ≤ (s.regs 0).toNat)

/-- registers that stay fixed through the body (`s` = the entry state) -/
def RecRegs (s S : State) : Prop :=
  S.sp = s.sp - 272#64 ∧ S.regs 29 = s.sp - 280#64 ∧ S.regs 28 = s.regs 28 ∧ S.regs 18 = s.regs 18

/-- memory facts that stay true through the body: the saved `x29`/`x30` and the frame -/
def RecMem (s : State) (M : Memory) : Prop :=
  M.readLE (s.sp.toNat - 280) 8 = (s.regs 29).toNat ∧ M.readLE (s.sp.toNat - 272) 8 = (s.regs 30).toNat ∧
  MemFrame s.mem M [(s.sp.toNat - 280, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 48)]

/-- a store of `k` bytes at `a`, inside the frame (not touching the caller's saved FP/LR words `[sp-8, sp+8)`) and apart from the
two saved words, keeps `RecMem` -/
theorem RecMem.write {s : State} {M : Memory} (h : RecMem s M) (a k v : Nat)
    (h1 : (s.sp.toNat - 280 ≤ a ∧ a + k ≤ s.sp.toNat - 8) ∨ (s.sp.toNat + 8 ≤ a ∧ a + k ≤ s.sp.toNat + 48))
    (hp : a + k ≤ s.sp.toNat - 280 ∨ s.sp.toNat - 264 ≤ a) (hsp : 280 ≤ s.sp.toNat) : RecMem s (M.writeLE a k v) := by
  obtain ⟨h3, h4, h6⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h3
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h4
  · rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h6.writeLE v (r := (s.sp.toNat - 280, s.sp.toNat - 8)) (by simp) h1 h2
    · exact h6.writeLE v (r := (s.sp.toNat + 8, s.sp.toNat + 48)) (by simp) h1 h2

theorem RecRegs.sp_toNat {s S : State} (h : RecRegs s S) (hsp : 280 ≤ s.sp.toNat) : S.sp.toNat + 272 = s.sp.toNat := by
  rw [h.1]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem ofNat_mod64 (e : Nat) : BitVec.ofNat 64 (e % 18446744073709551616) = BitVec.ofNat 64 e := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, Nat.mod_mod]

/-- `r0`: the 32-bit first approximation of `2^63 / yh` (`yh` the top 32 bits of the normalised top word) -/
def r0f (y3 : Nat) : Nat := if y3 / 2 ^ 32 = 2 ^ 31 then 2 ^ 32 - 1 else 2 ^ 63 / (y3 / 2 ^ 32)

theorem bv_eq_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

end Fv256.Arm64.RecipSeg
