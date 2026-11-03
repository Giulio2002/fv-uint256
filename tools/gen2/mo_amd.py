#!/usr/bin/env python3 -I
# mo_amd.py : writes lean/Fv256/Amd64/MoCases/{A..E}.lean (one per aliasing pattern of (z,x,y)) and lean/Fv256/Amd64/MulOverflow.lean
# (per-goal bullets: never `first | omega | janus_carry` over the big limb goals -- that blew 33 GB on arm64)
import os
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OPEN = "\nopen Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic\n\n"
HDR = "import Extracted\nimport Fv256.Spec\nimport Fv256.Util\n"
PATS = {'A': (('z','x','y'), ['z','x','y'], [('z','x'),('z','y'),('x','y')]),
        'B': (('z','z','y'), ['z','y'], [('z','y')]),
        'C': (('z','x','z'), ['z','x'], [('z','x')]),
        'D': (('z','x','x'), ['z','x'], [('z','x')]),
        'E': (('z','z','z'), ['z'], [])}
SP = "(s.regs regSP).toNat"
def stmt(n):
    (Z, X, Y), params, pairs = PATS[n]
    dj = "".join(f" ∧ (({a}.toNat + 32 ≤ {b}.toNat) ∨ ({b}.toNat + 32 ≤ {a}.toNat))" for a, b in pairs)
    stk = "".join(f" ∧ ({v}.toNat + 32 ≤ {SP} - 152 ∨ {SP} + 16 ≤ {v}.toNat)" for v in params)
    bufs = f"Buffer s {Z} 32 true ∧ Buffer s {X} 32 false ∧ Buffer s {Y} 32 false"
    L = f"theorem case{n} ({' '.join(params)} : BitVec 64) :\n    Ensures Extracted.program Extracted.entry [{Z}, {X}, {Y}]\n"
    L += f"      (fun s => StackGuardOK s 0 ∧ StackWritable s 152 16 ∧ {SP} % 8 = 0 ∧ {bufs}{dj}{stk})\n"
    L += f"      (fun s s' => s'.regs 0 = {Z} ∧\n        (s'.regs 3).toNat % 256 = (if Spec.W ≤ valueAt s {X} 32 * valueAt s {Y} 32 then 1 else 0) ∧\n"
    L += f"        valueAt s' {Z} 32 = Spec.mul (valueAt s {X} 32) (valueAt s {Y} 32) ∧\n        Util.OnlyWrites2 s.mem s'.mem {Z}.toNat 32 ({SP} - 152) 168) := by\n"
    L += "  intro ret hret s hs ⟨hg, ⟨hlow, hnw, hacc⟩, hal, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩" + "".join(f", hd{i}" for i in range(len(pairs)+len(params))) + "⟩\n"
    L += "  janus64_intro hs\n  have hgl := hg.load\n  have hgb := hg.below\n  have hnw2 := hg.noWrap\n  have hgr := hg.readable\n"
    L += "  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hal" + "".join(f" hd{i}" for i in range(len(pairs)+len(params))) + "\n"
    L += "  simp only [valueAt]\n  janus64_run [Util.readLE_32]\n"
    for v in params:
        for j in range(4):
            L += f"  have := Util.readLE8_lt s.mem {v}.toNat\n" if j == 0 else f"  have := Util.readLE8_lt s.mem ({v}.toNat + {8*j})\n"
    for v in {X, Y}:
        L += f"  have hv{v} : Janus.Arm64.Memory.readLE s.mem {v}.toNat 32 < 2 ^ 256 := by\n    simpa [Nat.reducePow] using Janus.Arm64.Memory.readLE_lt s.mem {v}.toNat 32\n"
    L += "  refine ⟨?_, ?_, ?_, ?_⟩\n"
    L += "  · first | rfl | simp\n"
    L += f"  · simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_mod]\n    refine Util.mo_flag8 _ _ _ _ _ _ hv{X} hv{Y} ?_ ?_ ?_ ?_\n" + "    · (simp only [Util.readLE_32, Spec.W, Nat.reducePow]; janus_carry)\n" * 4
    L += "  · simp only [Spec.mul, Spec.W, Nat.reducePow, Util.readLE_32]; janus_arith\n"
    L += "  · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]\n"
    return L
os.makedirs(ROOT + '/lean/Fv256/Amd64/MoCases', exist_ok=True)
for n in PATS:
    open(ROOT + f'/lean/Fv256/Amd64/MoCases/{n}.lean', 'w').write(
        HDR + OPEN + "namespace Fv256.Amd64.MulOverflow\n\nset_option exponentiation.threshold 600 in\nset_option maxHeartbeats 64000000 in\n" + stmt(n) + "\nend Fv256.Amd64.MulOverflow\n")

MAIN = HDR + "".join(f"import Fv256.Amd64.MoCases.{n}\n" for n in PATS) + '''
/-!
# `(*uint256.Int).MulOverflow(x, y *Int) (*Int, bool)` (amd64): `z = x * y mod 2^256` and the overflow flag

**Guarantee.** For all pointers `z`, `x`, `y` (`RAX`, `RBX`, `RCX`) with the 32 bytes at `z` writable and those at `x`, `y` readable (below `2^48`),
every pair of the three pointers equal or disjoint, the 168-byte window around the stack pointer (`StackWritable s 152 16`: the function's frame and
the extracted `umul` callee's) disjoint from the three objects, `RSP` 8-aligned, and a Go call whose stack check falls through (`StackGuardOK s 0`):
the call returns (no fault, no panic), obeys the ABI, returns `z` in `RAX`, the overflow flag in `RBX` (low byte) is `1` iff `x*y >= 2^256`, the number at `z`
afterwards is `Fv256.Spec.mul` of the numbers at `x` and `y` before the call, and no byte changes outside `z[0..32)` and the stack window.
One proof module per aliasing pattern of `(z, x, y)` (`MoCases/A..E`).
-/
''' + OPEN + "namespace Fv256.Amd64.MulOverflow\n\n" + '''def Alias (p q : BitVec 64) : Prop := p = q ∨ p.toNat + 32 ≤ q.toNat ∨ q.toNat + 32 ≤ p.toNat

set_option maxHeartbeats 64000000 in
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 152 16 ∧ (s.regs regSP).toNat % 8 = 0 ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Alias z x ∧ Alias z y ∧ Alias x y ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 152 ∨ (s.regs regSP).toNat + 16 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 152 ∨ (s.regs regSP).toNat + 16 ≤ x.toNat) ∧
        (y.toNat + 32 ≤ (s.regs regSP).toNat - 152 ∨ (s.regs regSP).toNat + 16 ≤ y.toNat))
      (fun s s' => s'.regs 0 = z ∧
        (s'.regs 3).toNat % 256 = (if Spec.W ≤ valueAt s x 32 * valueAt s y 32 then 1 else 0) ∧
        valueAt s' z 32 = Spec.mul (valueAt s x 32) (valueAt s y 32) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 152) 168) := by
  intro ret hret s hs ⟨hg, hst, hal, hz, hx, hy, hzx, hzy, hxy, hd1, hd2, hd3⟩
  rcases hzx with hzx | hzx
  · subst hzx
    rcases hzy with hzy | hzy
    · subst hzy
      exact caseE _ ret hret s hs ⟨hg, hst, hal, hz, hx, hy, hd1⟩
    · exact caseB _ _ ret hret s hs ⟨hg, hst, hal, hz, hx, hy, hzy, hd1, hd3⟩
  · rcases hzy with hzy | hzy
    · subst hzy
      exact caseC _ _ ret hret s hs ⟨hg, hst, hal, hz, hx, hy, hzx, hd1, hd2⟩
    · rcases hxy with hxy | hxy
      · subst hxy
        exact caseD _ _ ret hret s hs ⟨hg, hst, hal, hz, hx, hy, hzx, hd1, hd2⟩
      · exact caseA _ _ _ ret hret s hs ⟨hg, hst, hal, hz, hx, hy, hzx, hzy, hxy, hd1, hd2, hd3⟩

-- Witness: to be added once the cases verify (state as in Clone/amd64: guard register, stack window, wmem64-style memory).

end Fv256.Amd64.MulOverflow
'''
open(ROOT + '/lean/Fv256/Amd64/MulOverflow.lean', 'w').write(MAIN)
