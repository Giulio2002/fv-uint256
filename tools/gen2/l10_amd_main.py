#!/usr/bin/env python3 -I
# l10_amd_main.py : writes lean/Fv256/Proofs/Amd64/L10Cases/Zero.lean and lean/Fv256/Proofs/Amd64/Log10.lean (dispatcher over the 256 case modules)
import os
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OPEN = "\nopen Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic\n\n"
def xa(j): return '(x.toNat + %d)' % (8*j) if j else 'x.toNat'
def la(j): return f"s.mem.readLE {xa(j)} 8"
PRE = """StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB)"""
INTRO = "⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB"
HDR = "import Extracted\nimport Fv256.Spec\nimport Fv256.Util\nimport Fv256.Amd64.L10Defs\n"
# zero case
z = HDR + OPEN + "namespace Fv256.Amd64.Log10\n\n"
z += "set_option maxHeartbeats 64000000 in\ntheorem zero (x : BitVec 64) :\n    Ensures Extracted.program Extracted.entry [x]\n      (fun s => " + PRE + " ∧\n        " + " ∧ ".join(la(j) + " = 0" for j in range(4)) + ")\n"
z += "      (fun s s' => (s'.regs 0).toNat = 0) := by\n  intro ret hret s hs " + INTRO + ", hz0, hz1, hz2, hz3⟩\n  janus64_intro hs\n  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB\n"
z += "".join(f"  have hw{j} : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE {xa(j)} 8) = s.mem.readLE {xa(j)} 8 := fun v => by\n    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]\n" for j in range(4))
z += "  have hwr : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (s.regs 4).toNat 8) = s.mem.readLE (s.regs 4).toNat 8 := fun v => by\n    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]\n"
z += "  janus64_run [hwr, hz0, hz1, hz2, hz3, hw0, hw1, hw2, hw3]\n  all_goals omega\n\nend Fv256.Amd64.Log10\n"
os.makedirs(ROOT + '/lean/Fv256/Proofs/Amd64/L10Cases', exist_ok=True)
open(ROOT + '/lean/Fv256/Proofs/Amd64/L10Cases/Zero.lean', 'w').write(z)
# main
M = HDR + "import Fv256.Proofs.Amd64.L10Cases.Zero\n"
for k in range(4):
    for m in range(1, 65): M += f"import Fv256.Proofs.Amd64.L10Cases.C{k}_{m}\n"
M += '''
/-!
# `(*uint256.Int).Log10() uint` (amd64, default GOAMD64=v1 build)

**Guarantee.** For every pointer `x` (receiver, `RAX`) such that the 32 bytes at `x` are readable (below `2^48`) and the return-address slot
and the callee's 8-byte frame word are writable and do not overlap `x`, the call returns (no fault, no panic), obeys the ABI, and the result
`r` satisfies, with `v` the 256-bit number at `x` read before the call: `v = 0 → r = 0` and `v ≠ 0 → 10^r ≤ v < 10^(r+1)`
(so `r = ⌊log10 v⌋`, determined uniquely).

**Requirements.** The Go globals `uint256.pows64` (`[20]uint64`) and `uint256.pows` (`[60]Int`), addressed by `Extracted.dataAddr` live in writable
`.noptrdata`, which the extractor does not copy; `Tabs64`/`TabsBig` (Fv256.Amd64.L10Defs) assume that they are readable, disjoint from the
callee's stack window and hold the powers of ten (only `10^20..10^77` of `pows` are claimed and read).

**Note.** The default build uses `BSR` on the lowest limb, which may be zero (destination undefined by the ISA); the zero case holds for every value of
that undefined result (it is replaced by `CMOVE`). Verified against the Janus BSF/BSR-of-zero model (`bsrbsf` branch); see `COVERAGE.md`.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call state (tables in memory) satisfies the preconditions; `Witness.returns`: for 12345 the call returns 4.
-/
''' + OPEN + "namespace Fv256.Amd64.Log10\n\n"
for k in range(4):
    zs = [f"{la(j)} = 0" for j in range(3, k, -1)]
    pre = "fun s => " + PRE + "".join(" ∧ " + t for t in zs) + f" ∧ {la(k)} ≠ 0"
    names = "".join(f", hz{j}" for j in range(3, k, -1))
    M += f"set_option maxHeartbeats 64000000 in\ntheorem disp{k} (x : BitVec 64) :\n    Ensures Extracted.program Extracted.entry [x]\n      ({pre})\n"
    M += "      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by\n"
    M += f"  intro ret hret s hs {INTRO}{names}, hnz⟩\n"
    M += f"  have hbd := Util.bitLen_bounds ({la(k)}) hnz\n  have hlt := Util.readLE8_lt s.mem {xa(k)}\n"
    M += f"  have hm1 : 1 ≤ Spec.bitLen ({la(k)}) := by\n    have := hbd.1; have h1 := Nat.pos_of_ne_zero hnz; unfold Spec.bitLen; rw [if_neg hnz]; omega\n"
    M += f"  have hm2 : Spec.bitLen ({la(k)}) ≤ 64 := by\n    have := hbd.1; refine Classical.byContradiction fun h => ?_\n    have : 2 ^ 64 ≤ 2 ^ (Spec.bitLen ({la(k)}) - 1) := Nat.pow_le_pow_right (by omega) (by omega)\n    omega\n"
    M += f"  generalize Spec.bitLen ({la(k)}) = m at hbd hm1 hm2\n  obtain ⟨lo, hi⟩ := hbd\n"
    M += "  rcases (show " + " ∨ ".join(f"m = {m}" for m in range(1, 65)) + " by omega) with " + " | ".join(["rfl"]*64) + "\n"
    for m in range(1, 65):
        M += f"  · exact c{k}_{m} x ret hret s hs {INTRO}{names}, lo, hi⟩\n"
    M += "\n"
M += "set_option maxHeartbeats 64000000 in\ntheorem correctness (x : BitVec 64) :\n    Ensures Extracted.program Extracted.entry [x]\n      (fun s => " + PRE + ")\n"
M += "      (fun s s' => (valueAt s x 32 = 0 → (s'.regs 0).toNat = 0) ∧\n        (valueAt s x 32 ≠ 0 → 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1))) := by\n"
M += "  intro ret hret s hs hpre\n  have hv : valueAt s x 32 = " + " + ".join((f"2 ^ {64*j} * " if j else "") + la(j) for j in range(4)) + " := Util.readLE_32 s.mem x.toNat\n"
M += "".join(f"  have hl{j} := Util.readLE8_lt s.mem {xa(j)}\n" for j in range(4))
M += "  obtain " + INTRO + "⟩ := hpre\n"
def args(k): return INTRO + "".join(f", hz{j}" for j in range(3, k, -1)) + "⟩"
M += "  by_cases h3 : " + la(3) + " = 0\n"
M += f"  · by_cases h2 : {la(2)} = 0\n"
M += f"    · by_cases h1 : {la(1)} = 0\n"
M += f"      · by_cases h0 : {la(0)} = 0\n"
M += f"        · have := zero x ret hret s hs {INTRO}, h0, h1, h2, h3⟩\n"
M += f"          refine this.mono fun s' ⟨hab, hr⟩ => ⟨hab, fun _ => hr, fun hne => (hne (by omega)).elim⟩\n"
M += f"        · have := disp0 x ret hret s hs {INTRO}, h3, h2, h1, h0⟩\n"
M += f"          refine this.mono fun s' ⟨hab, hr⟩ => ⟨hab, fun hz => by omega, fun _ => hr⟩\n"
M += f"      · have := disp1 x ret hret s hs {INTRO}, h3, h2, h1⟩\n"
M += f"        refine this.mono fun s' ⟨hab, hr⟩ => ⟨hab, fun hz => by omega, fun _ => hr⟩\n"
M += f"    · have := disp2 x ret hret s hs {INTRO}, h3, h2⟩\n"
M += f"      refine this.mono fun s' ⟨hab, hr⟩ => ⟨hab, fun hz => by omega, fun _ => hr⟩\n"
M += f"  · have := disp3 x ret hret s hs {INTRO}, h3⟩\n"
M += f"    refine this.mono fun s' ⟨hab, hr⟩ => ⟨hab, fun hz => by omega, fun _ => hr⟩\n\n"
M += open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'l10_amd_witness.lean')).read()
open(ROOT + '/lean/Fv256/Proofs/Amd64/Log10.lean', 'w').write(M)
