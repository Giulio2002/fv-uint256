import Extracted
import Fv256.Spec.AddMod
import Fv256.Arm64.Machine
import Fv256.Proofs.Arm64.AddModMain

/-!
# arm64: the compiled `(*uint256.Int).AddMod` implements `Spec.addMod`  (`Fv256/Spec/AddMod.lean`)

`z.AddMod(x, y, m)` (`X0..X3`) returns normally with `X0 = z`, leaves `Spec.addMod x y m` (`(x + y) mod m`, or `0` for `m = 0`)
in `z`, and writes only `z[0, 32)` and its own stack frame. `z` is equal to or disjoint from each of `x`, `y`, `m`.
The proof is `Fv256/Proofs/Arm64/AddModMain.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Fv256.Arm64

namespace Fv256.Arm64.AddMod

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`GuardOK`), `SP` is 16-byte aligned with
856 bytes below it and 16 above usable, the binary's read-only data is loaded. Buffers: `z` writable, `x`, `y`, `m` readable,
32 bytes each, none overlapping the frame `[SP-856, SP+16)`; `z` is equal-or-disjoint from `x`, `y`, `m`; the goroutine's
`g` words at `X28` are outside the frame and do not overlap `z`. -/
def Pre (z x y m : BitVec 64) (s : State) : Prop :=
  GuardOK s 816 ∧ s.sp.toNat % 16 = 0 ∧ 856 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 48 ∧
  s.mem.accessible (s.sp.toNat - 856) 872 true = true ∧ Extracted.program.DataLoaded s.mem ∧
  ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 856 ∨ s.sp.toNat + 16 ≤ (s.regs 28).toNat + 16) ∧
  Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Ptr32 s.mem m false ∧
  Janus.Spec.Disjoint z.toNat 32 (s.sp.toNat - 856) 872 ∧ Janus.Spec.Disjoint x.toNat 32 (s.sp.toNat - 856) 872 ∧
  Janus.Spec.Disjoint y.toNat 32 (s.sp.toNat - 856) 872 ∧ Janus.Spec.Disjoint m.toNat 32 (s.sp.toNat - 856) 872 ∧
  Alias32 z m ∧ Alias32 z x ∧ Alias32 z y ∧
  ((s.regs 28).toNat + 24 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 28).toNat + 16)

/-- POSTCONDITION: `X0 = z`; the number at `z` is `Spec.addMod` of the numbers at `x`, `y`, `m` BEFORE the call; memory changed
only in `z[0, 32)` and the callee's stack frame. -/
def Post (z x y m : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  Janus.Spec.val256 s'.mem z.toNat = Fv256.Spec.addMod (Janus.Spec.val256 s.mem x.toNat) (Janus.Spec.val256 s.mem y.toNat)
    (Janus.Spec.val256 s.mem m.toNat) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 856, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 16)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x y m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, m] (Pre z x y m) (Post z x y m) :=
  Fv256.Arm64.AddModMain.correctness_proof z x y m

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.AddMod(x, x, x)`) satisfies `Pre` and its call returns with `Post`. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y, m] s ∧ Pre z x y m s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y m s s' :=
  Fv256.Arm64.AddModMain.Wit.nonvacuous

end Witness

end Fv256.Arm64.AddMod
