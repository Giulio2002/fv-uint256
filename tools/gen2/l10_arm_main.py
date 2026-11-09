#!/usr/bin/env python3 -I
# l10_arm_main.py : writes lean/Fv256/Proofs/Arm64/L10Cases/Zero.lean and lean/Fv256/Proofs/Arm64/Log10.lean (the dispatcher over the 256 case modules)
import os
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OPEN = "\nopen Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec\n\n"
def la(j): return f"s.mem.readLE (x.toNat + {8*j}) 8" if j else "s.mem.readLE x.toNat 8"
PRE = ("GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧\n"
       "        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32")
INTRO = "⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB"
# --- zero case
z = "import Extracted\nimport Fv256.Spec\nimport Fv256.Util\nimport Fv256.Arm64.L10Defs\n" + OPEN + "namespace Fv256.Arm64.Log10\n\n"
z += "set_option maxHeartbeats 64000000 in\ntheorem zero (x : BitVec 64) :\n    Ensures Extracted.program Extracted.entry [x]\n      (fun s => " + PRE + " ∧\n        " + " ∧ ".join(la(j) + " = 0" for j in range(4)) + ")\n"
z += "      (fun s s' => (s'.regs 0).toNat = 0) := by\n  intro ret hret s hs " + INTRO + ", hz0, hz1, hz2, hz3⟩\n  janus_intro hs\n  simp only [Disjoint] at hdis hd64 hdB\n  janus_data hd [hw]\n  janus_run [hz0, hz1, hz2, hz3]\n  all_goals omega\n\nend Fv256.Arm64.Log10\n"
os.makedirs(ROOT + '/lean/Fv256/Proofs/Arm64/L10Cases', exist_ok=True)
open(ROOT + '/lean/Fv256/Proofs/Arm64/L10Cases/Zero.lean', 'w').write(z)
# --- main
M = "import Extracted\nimport Fv256.Spec\nimport Fv256.Util\nimport Fv256.Arm64.L10Defs\nimport Fv256.Arm64.L10Cases.Zero\n"
for k in range(4):
    for m in range(1, 65): M += f"import Fv256.Proofs.Arm64.L10Cases.C{k}_{m}\n"
M += '''
/-!
# `(*uint256.Int).Log10() int` (arm64)

**Guarantee.** For every pointer `x` (receiver, `X0`) such that the 32 bytes at `x` are readable (below `2^48`), the call
returns (no fault, no panic), obeys the ABI, and the result `r = X0` satisfies, with `v` the 256-bit number at `x` read
before the call: `v = 0 → r = 0` and `v ≠ 0 → 10^r ≤ v < 10^(r+1)` (so `r = ⌊log10 v⌋`, determined uniquely).

**Requirements.** The Go runtime globals `uint256.pows64` (`[20]uint64`, at `0x1b0dc0`) and `uint256.pows` (`[60]Int`, at
`0x1b1f40`) hold the powers of ten `10^i` (i < 20) and `10^(20+i)`: they live in writable data (`.noptrdata`), so the
extractor does not take their contents from the binary; `Tabs64`/`TabsBig` (Fv256.Arm64.L10Defs) state that they are readable
and hold these values (nothing in the program writes them), and are disjoint from the callee's 32-byte stack window.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call state (with the tables in memory) satisfies the preconditions;
`Witness.returns`: for the value 12345 the call returns 4.
-/
''' + OPEN + "namespace Fv256.Arm64.Log10\n\n"
for k in range(4):
    zs = [f"{la(j)} = 0" for j in range(3, k, -1)]
    pre = "fun s => " + PRE + "".join(" ∧ " + t for t in zs) + f" ∧ {la(k)} ≠ 0"
    names = "".join(f", hz{j}" for j in range(3, k, -1))
    M += f"set_option maxHeartbeats 64000000 in\ntheorem disp{k} (x : BitVec 64) :\n    Ensures Extracted.program Extracted.entry [x]\n      ({pre})\n"
    M += "      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by\n"
    M += f"  intro ret hret s hs {INTRO}{names}, hnz⟩\n"
    M += f"  have hbd := Util.bitLen_bounds ({la(k)}) hnz\n  have hlt := Util.readLE8_lt s.mem {'x.toNat' if k == 0 else '(x.toNat + %d)' % (8*k)}\n"
    M += f"  have hm1 : 1 ≤ Spec.bitLen ({la(k)}) := by\n    have := hbd.1; have h1 := Nat.pos_of_ne_zero hnz; unfold Spec.bitLen; rw [if_neg hnz]; omega\n"
    M += f"  have hm2 : Spec.bitLen ({la(k)}) ≤ 64 := by\n    have := hbd.1; refine Classical.byContradiction fun h => ?_\n    have : 2 ^ 64 ≤ 2 ^ (Spec.bitLen ({la(k)}) - 1) := Nat.pow_le_pow_right (by omega) (by omega)\n    omega\n"
    M += f"  generalize Spec.bitLen ({la(k)}) = m at hbd hm1 hm2\n  obtain ⟨lo, hi⟩ := hbd\n"
    M += "  rcases (show " + " ∨ ".join(f"m = {m}" for m in range(1, 65)) + " by omega) with " + " | ".join(["rfl"]*64) + "\n"
    for m in range(1, 65):
        M += f"  · exact c{k}_{m} x ret hret s hs {INTRO}{names}, lo, hi⟩\n"
    M += "\n"
# main
M += "set_option maxHeartbeats 64000000 in\ntheorem correctness (x : BitVec 64) :\n    Ensures Extracted.program Extracted.entry [x]\n      (fun s => " + PRE + ")\n"
M += "      (fun s s' => (val256 s.mem x.toNat = 0 → (s'.regs 0).toNat = 0) ∧\n        (val256 s.mem x.toNat ≠ 0 → 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1))) := by\n"
M += "  intro ret hret s hs hpre\n  have hv : val256 s.mem x.toNat = " + " + ".join((f"2 ^ {64*j} * " if j else "") + la(j) for j in range(4)) + " := Util.readLE_32 s.mem x.toNat\n"
M += "".join(f"  have hl{j} := Util.readLE8_lt s.mem {'x.toNat' if j == 0 else '(x.toNat + %d)' % (8*j)}\n" for j in range(4))
M += "  obtain ⟨⟨hg1, hg2, hg3⟩, hst, hd, hx, hdis, hT64, hTB, hd64, hdB⟩ := hpre\n"
def mk(k): return "⟨⟨hg1, hg2, hg3⟩, hst, hd, hx, hdis, hT64, hTB, hd64, hdB" + "".join(f", hz{j}" for j in range(3, k, -1)) + (", hnz" if k >= 0 else "") + "⟩"
M += "  by_cases h3 : " + la(3) + " = 0\n"
# explicit nesting
M += f"  · by_cases h2 : {la(2)} = 0\n"
M += f"    · by_cases h1 : {la(1)} = 0\n"
M += f"      · by_cases h0 : {la(0)} = 0\n"
M += f"        · have := zero x ret hret s hs ⟨⟨hg1, hg2, hg3⟩, hst, hd, hx, hdis, hT64, hTB, hd64, hdB, h0, h1, h2, h3⟩\n"
M += f"          refine this.mono fun s' ⟨hab, hr⟩ => ⟨hab, fun _ => hr, fun hne => (hne (by omega)).elim⟩\n"
M += f"        · have := disp0 x ret hret s hs ⟨⟨hg1, hg2, hg3⟩, hst, hd, hx, hdis, hT64, hTB, hd64, hdB, h3, h2, h1, h0⟩\n"
M += f"          refine this.mono fun s' ⟨hab, hr⟩ => ⟨hab, fun hz => by omega, fun _ => hr⟩\n"
M += f"      · have := disp1 x ret hret s hs ⟨⟨hg1, hg2, hg3⟩, hst, hd, hx, hdis, hT64, hTB, hd64, hdB, h3, h2, h1⟩\n"
M += f"        refine this.mono fun s' ⟨hab, hr⟩ => ⟨hab, fun hz => by omega, fun _ => hr⟩\n"
M += f"    · have := disp2 x ret hret s hs ⟨⟨hg1, hg2, hg3⟩, hst, hd, hx, hdis, hT64, hTB, hd64, hdB, h3, h2⟩\n"
M += f"      refine this.mono fun s' ⟨hab, hr⟩ => ⟨hab, fun hz => by omega, fun _ => hr⟩\n"
M += f"  · have := disp3 x ret hret s hs ⟨⟨hg1, hg2, hg3⟩, hst, hd, hx, hdis, hT64, hTB, hd64, hdB, h3⟩\n"
M += f"    refine this.mono fun s' ⟨hab, hr⟩ => ⟨hab, fun hz => by omega, fun _ => hr⟩\n\n"
M += open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'l10_arm_witness.lean')).read()
open(ROOT + '/lean/Fv256/Proofs/Arm64/Log10.lean', 'w').write(M)
