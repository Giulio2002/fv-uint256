import Fv256.Spec
import Fv256.Util
import Fv256.Arm64.SfdProg

/-!
# `(*uint256.Int).Mul` as a callee of `fromDecimal` (arm64)

The `Mul.correctness` proof of `Fv256.Arm64.Mul`, re-proved as a `Summary` on the library program (the receiver `z` in
`X0`, `x` in `X1`, `y` in `X2`; any overlap between `z`, `x`, `y` is allowed).  A leaf: no stack use.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SfdMul

abbrev mulEntry : Nat := segAddr Fv256.Arm64.SfdProg.program "github.com/holiman/uint256.(*Int).Mul"

def MulPre (z x y : BitVec 64) (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧
  s.regs 0 = z ∧ s.regs 1 = x ∧ s.regs 2 = y ∧ Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
  Aliasing z x ∧ Aliasing z y ∧ Aliasing x y

def MulPost (z x y : BitVec 64) (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 0 = z ∧
  val256 s'.mem z.toNat = Spec.mul (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32)]

set_option maxHeartbeats 16000000 in
theorem mul_sum (impl : List Segment) (z x y : BitVec 64) :
    Summary (Fv256.Arm64.SfdProg.program.link impl) mulEntry (MulPre z x y) (MulPost z x y) := by
  intro s hpc ⟨hl1, hl2, h0, h1, h2, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, hzx, hzy, hxy⟩

  rcases hzx with rfl | hzx <;> rcases hzy with rfl | hzy <;> rcases hxy with h | hxy
  all_goals try subst h
  all_goals simp only [Disjoint] at *
  all_goals first
    | (exfalso; omega)
    | (janus_run [MulPost]
       all_goals (repeat' refine And.intro ?_ ?_)
       all_goals first
         | (simp [setReg_apply, h0]; done)
         | janus_frame
         | (clear h0 h1 h2 hl1 hl2 hz hz' hx hx' hy hy' hpc; (try have := Util.readLE8_lt s.mem (z.toNat)); (try have := Util.readLE8_lt s.mem (z.toNat + 8)); (try have := Util.readLE8_lt s.mem (z.toNat + 16)); (try have := Util.readLE8_lt s.mem (z.toNat + 24)); (try have := Util.readLE8_lt s.mem (x.toNat)); (try have := Util.readLE8_lt s.mem (x.toNat + 8)); (try have := Util.readLE8_lt s.mem (x.toNat + 16)); (try have := Util.readLE8_lt s.mem (x.toNat + 24)); (try have := Util.readLE8_lt s.mem (y.toNat)); (try have := Util.readLE8_lt s.mem (y.toNat + 8)); (try have := Util.readLE8_lt s.mem (y.toNat + 16)); (try have := Util.readLE8_lt s.mem (y.toNat + 24))
            simp only [Spec.mul, Spec.W, Nat.reducePow]
            first | janus_arith | trace_state))
