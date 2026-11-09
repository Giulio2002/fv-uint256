#!/usr/bin/env python3 -I
# mo_arm.py : writes lean/Fv256/Proofs/Arm64/MoCases/{A,B,C,D,E}.lean (one module per aliasing pattern of (z, x, y)) and lean/Fv256/Proofs/Arm64/MulOverflow.lean
import os
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OPEN = "\nopen Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec\n\n"
HDR = "import Extracted\nimport Fv256.Spec\nimport Fv256.Util\n"
# pattern: name, (Z, X, Y) variable names, parameters, extra disjointness (pairs of distinct pointers)
PATS = {
 'A': (('z', 'x', 'y'), ['z', 'x', 'y'], [('z', 'x'), ('z', 'y'), ('x', 'y')]),
 'B': (('z', 'z', 'y'), ['z', 'y'], [('z', 'y')]),
 'C': (('z', 'x', 'z'), ['z', 'x'], [('z', 'x')]),
 'D': (('z', 'x', 'x'), ['z', 'x'], [('z', 'x')]),
 'E': (('z', 'z', 'z'), ['z'], []),
}
def stmt(name):
    (Z, X, Y), params, pairs = PATS[name]
    dj = "".join(f" ∧ Disjoint32 {a}.toNat {b}.toNat" for a, b in pairs)
    stk = "".join(f" ∧ Disjoint {v}.toNat 32 (s.sp.toNat - 240) 256" for v in params)
    L = f"theorem case{name} ({' '.join(params)} : BitVec 64) :\n    Ensures Extracted.program Extracted.entry [{Z}, {X}, {Y}]\n"
    L += f"      (fun s => GuardOK s 0 ∧ StackOK s 240 16 ∧ Ptr32 s.mem {Z} true ∧ Ptr32 s.mem {X} false ∧ Ptr32 s.mem {Y} false{dj}{stk})\n"
    L += f"      (fun s s' => s'.regs 0 = {Z} ∧\n        (s'.regs 1).toNat = (if Spec.W ≤ val256 s.mem {X}.toNat * val256 s.mem {Y}.toNat then 1 else 0) ∧\n"
    L += f"        val256 s'.mem {Z}.toNat = Spec.mul (val256 s.mem {X}.toNat) (val256 s.mem {Y}.toNat) ∧\n        Util.OnlyWrites2 s.mem s'.mem {Z}.toNat 32 (s.sp.toNat - 240) 256) := by\n"
    L += "  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩" + "".join(f", hd{i}" for i in range(len(pairs) + len(params))) + "⟩\n"
    L += "  janus_intro hs\n  simp only [Disjoint32, Disjoint] at *\n  janus_run\n"
    haves = []
    for v in params:
        for j in range(4):
            haves.append(f"have := Util.readLE8_lt s.mem {v}.toNat" if j == 0 else f"have := Util.readLE8_lt s.mem ({v}.toNat + {8*j})")
    L += "  " + "\n  ".join(haves) + "\n"
    L += "  refine ⟨?_, ?_, ?_⟩\n"
    L += "  · refine Util.mo_flag _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_\n    · omega\n    · omega\n" + "    · (simp only [Spec.W, Nat.reducePow]; janus_arith)\n" * 4
    L += "  · simp only [Spec.mul, Spec.W, Nat.reducePow]; janus_arith\n"
    L += "  · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]\n"
    return L
os.makedirs(ROOT + '/lean/Fv256/Proofs/Arm64/MoCases', exist_ok=True)
for n in PATS:
    open(ROOT + f'/lean/Fv256/Proofs/Arm64/MoCases/{n}.lean', 'w').write(
        HDR + OPEN + "namespace Fv256.Arm64.MulOverflow\n\nset_option maxHeartbeats 64000000 in\n" + stmt(n) + "\nend Fv256.Arm64.MulOverflow\n")

MAIN = HDR + "".join(f"import Fv256.Proofs.Arm64.MoCases.{n}\n" for n in PATS) + '''
/-!
# `(*uint256.Int).MulOverflow(x, y *Int) (*Int, bool)` (arm64): `z = x * y mod 2^256` and the overflow flag

**Guarantee.** For all pointers `z`, `x`, `y` (`X0` receiver, `X1`, `X2`) with the 32 bytes at `z` writable and those at `x`, `y` readable
(below `2^48`), every pair of the three pointers equal or disjoint, the 256-byte window below the stack pointer (`StackOK s 240 16`: the
function's frame and the extracted `umul` callee's) disjoint from the three objects, and a Go call whose stack check falls through
(`GuardOK s 0`): the call returns (no fault, no panic), obeys the ABI, returns `z` in `X0`, the overflow flag in `X1` is `1` iff
`x*y >= 2^256`, the number at `z` afterwards is `Fv256.Spec.mul` of the numbers at `x` and `y` before the call, and no byte changes outside
`z[0..32)` and the stack window. One proof module per aliasing pattern of `(z, x, y)` (`MoCases/A..E`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z` with flag `0` and value `0`.
-/
''' + OPEN + "namespace Fv256.Arm64.MulOverflow\n\n" + '''set_option maxHeartbeats 64000000 in
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => GuardOK s 0 ∧ StackOK s 240 16 ∧ Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
        Aliasing z x ∧ Aliasing z y ∧ Aliasing x y ∧
        Disjoint z.toNat 32 (s.sp.toNat - 240) 256 ∧ Disjoint x.toNat 32 (s.sp.toNat - 240) 256 ∧
        Disjoint y.toNat 32 (s.sp.toNat - 240) 256)
      (fun s s' => s'.regs 0 = z ∧
        (s'.regs 1).toNat = (if Spec.W ≤ val256 s.mem x.toNat * val256 s.mem y.toNat then 1 else 0) ∧
        val256 s'.mem z.toNat = Spec.mul (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 240) 256) := by
  intro ret hret s hs ⟨hg, hst, hz, hx, hy, hzx, hzy, hxy, hd1, hd2, hd3⟩
  rcases hzx with hzx | hzx
  · subst hzx
    rcases hzy with hzy | hzy
    · subst hzy
      exact caseE _ ret hret s hs ⟨hg, hst, hz, hx, hy, hd1⟩
    · exact caseB _ _ ret hret s hs ⟨hg, hst, hz, hx, hy, hzy, hd1, hd3⟩
  · rcases hzy with hzy | hzy
    · subst hzy
      exact caseC _ _ ret hret s hs ⟨hg, hst, hz, hx, hy, hzx, hd1, hd2⟩
    · rcases hxy with hxy | hxy
      · subst hxy
        exact caseD _ _ ret hret s hs ⟨hg, hst, hz, hx, hy, hzx, hd1, hd2⟩
      · exact caseA _ _ _ ret hret s hs ⟨hg, hst, hz, hx, hy, hzx, hzy, hxy, hd1, hd2, hd3⟩

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then x else if i = 2 then x
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, x] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

theorem hpre : GuardOK s0 0 ∧ StackOK s0 240 16 ∧ Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧ Ptr32 s0.mem x false ∧
    Aliasing z x ∧ Aliasing z x ∧ Aliasing x x ∧
    Disjoint z.toNat 32 (s0.sp.toNat - 240) 256 ∧ Disjoint x.toNat 32 (s0.sp.toNat - 240) 256 ∧
    Disjoint x.toNat 32 (s0.sp.toNat - 240) 256 :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, Or.inr (by unfold Disjoint32 Disjoint z x; decide), Or.inr (by unfold Disjoint32 Disjoint z x; decide), Or.inl rfl,
    by unfold Disjoint z; decide, by unfold Disjoint x; decide, by unfold Disjoint x; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧
    (GuardOK s 0 ∧ StackOK s 240 16 ∧ Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
      Aliasing z x ∧ Aliasing z y ∧ Aliasing x y ∧
      Disjoint z.toNat 32 (s.sp.toNat - 240) 256 ∧ Disjoint x.toNat 32 (s.sp.toNat - 240) 256 ∧
      Disjoint y.toNat 32 (s.sp.toNat - 240) 256) :=
  ⟨ret, s0, z, x, x, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ (s'.regs 1).toNat = 0 ∧ val256 s'.mem z.toNat = 0 := by
  refine (correctness z x x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · rw [h.2.2.1]; decide
  · rw [h.2.2.2.1]; decide

end Witness

end Fv256.Arm64.MulOverflow
'''
open(ROOT + '/lean/Fv256/Proofs/Arm64/MulOverflow.lean', 'w').write(MAIN)
