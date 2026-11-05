import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SumC64

/-!
# `(*uint256.Int).Mul` as a callee of `fromDecimal` (amd64)

The `Mul.correctness` proof of `Fv256.Amd64.Mul`, re-proved as a `Summary` on this extraction (the receiver `z` in `RAX`,
`x` in `RBX`, `y` in `RCX`; any overlap between `z`, `x`, `y` is allowed).
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.C

namespace Fv256.Amd64.SfdMul

abbrev mulEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).Mul"

def MulPre (z x y : BitVec 64) (s : State) : Prop :=
  RetOK s ∧ s.regs 0 = z ∧ s.regs 3 = x ∧ s.regs 1 = y ∧ StackWritable s 16 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
    Buffer s y 32 false ∧
    (z.toNat + 32 ≤ (s.regs regSP).toNat - 16 ∨ (s.regs regSP).toNat + 8 ≤ z.toNat) ∧
    (x.toNat + 32 ≤ (s.regs regSP).toNat - 16 ∨ (s.regs regSP).toNat ≤ x.toNat) ∧
    (y.toNat + 32 ≤ (s.regs regSP).toNat - 16 ∨ (s.regs regSP).toNat ≤ y.toNat)

def MulPost (z x y : BitVec 64) (s s' : State) : Prop :=
  Kept s s' ∧ s'.regs 0 = z ∧ valueAt s' z 32 = Spec.mul (valueAt s x 32) (valueAt s y 32) ∧
    Janus.MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 16, (s.regs regSP).toNat)]

set_option maxHeartbeats 16000000 in
theorem mul_sum (z x y : BitVec 64) : Summary Extracted.program mulEntry (MulPre z x y) (MulPost z x y) := by
  intro s hpc ⟨⟨hr1, hr2, hx15, hdf⟩, h0, h3, h1, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, hds, hdx, hdy⟩
  simp only [regSP] at hacc hnw hds hlow hdx hdy
  all_goals first
    | (exfalso; omega)
    | (janus64_run [Util.readLE_32, MulPost, Kept, valueAt, Spec.mul, regSP]
       all_goals ((try have := Util.readLE8_lt s.mem (z.toNat)); (try have := Util.readLE8_lt s.mem (z.toNat + 8)); (try have := Util.readLE8_lt s.mem (z.toNat + 16)); (try have := Util.readLE8_lt s.mem (z.toNat + 24)); (try have := Util.readLE8_lt s.mem (x.toNat)); (try have := Util.readLE8_lt s.mem (x.toNat + 8)); (try have := Util.readLE8_lt s.mem (x.toNat + 16)); (try have := Util.readLE8_lt s.mem (x.toNat + 24)); (try have := Util.readLE8_lt s.mem (y.toNat)); (try have := Util.readLE8_lt s.mem (y.toNat + 8)); (try have := Util.readLE8_lt s.mem (y.toNat + 16)); (try have := Util.readLE8_lt s.mem (y.toNat + 24)); skip)
       all_goals (
         refine ⟨?_, ?_⟩
         · simp only [Spec.W, Nat.reducePow, BitVec.toNat_mul, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reduceMod]
           janus64_arith
         · janus_frame))

end Fv256.Amd64.SfdMul
