#!/usr/bin/env python3 -I
# l10_arm.py [k:m ...] : writes lean/Fv256/Arm64/Log10.lean and lean/Fv256/Arm64/L10Cases/C<k>_<m>.lean
# (one module per (index k of the top nonzero limb, bit length m of that limb); the zero input is case Zero)
import os, sys
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
A64, ABIG = 1772992, 1777472
args = sys.argv[1:]
cases = [tuple(map(int, a.split(':'))) for a in args] or [(k, m) for k in range(4) for m in range(1, 65)]
HDR = "import Extracted\nimport Fv256.Spec\nimport Fv256.Util\nimport Fv256.Arm64.L10Defs\n"
OPEN = "\nopen Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec\n\n"
def tval(b): return (1233 * b + 1233) >> 12
def limbs(k, m):
    L = []
    for j in range(3, -1, -1):
        a = f"s.mem.readLE (x.toNat + {8*j}) 8" if j else "s.mem.readLE x.toNat 8"
        if j > k: L.append(f"{a} = 0")
        elif j == k: L.append(f"2 ^ {m-1} ≤ {a} ∧ {a} < 2 ^ {m}")
    return " ∧ ".join(L)
def xa(j): return '(x.toNat + %d)' % (8*j) if j else 'x.toNat'
def pat(k):
    return ', '.join([f'hz{j}' for j in range(3, k, -1)] + ['hl1', 'hl2'])
def zs(k):
    return ''.join(f', hz{j}' for j in range(3, k, -1))
def case(k, m):
    b = 64 * k + m
    t = tval(b)
    top = f"s.mem.readLE (x.toNat + {8*k}) 8" if k else "s.mem.readLE x.toNat 8"
    L = []
    L.append("set_option maxHeartbeats 64000000 in")
    L.append(f"theorem c{k}_{m} (x : BitVec 64) :")
    L.append("    Ensures Extracted.program Extracted.entry [x]")
    L.append("      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧")
    L.append("        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint 1772992 160 (s.sp.toNat - 32) 32 ∧ Disjoint 1777472 1920 (s.sp.toNat - 32) 32 ∧")
    L.append("        " + limbs(k, m) + ")")
    L.append("      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by")
    L.append("  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, " + pat(k) + "⟩")
    L.append("  janus_intro hs")
    L.append("  simp only [Disjoint] at hdis hd64 hdB")
    L.append("  janus_data hd [hw]")
    L.append(f"  have hc : clzNat 64 ({top}) = {64-m} := by")
    L.append(f"    have := Util.clz_bl 64 ({top}) (Util.readLE8_lt s.mem _)")
    L.append(f"    have h2 : Spec.bitLen ({top}) = {m} := Util.bitLen_of_range _ {m} (by omega) (by omega) (by omega)")
    L.append("    omega")
    extra = ""
    if t < 20:
        L.append(f"  have hTv : s.mem.readLE {A64 + 8*t} 8 = {10**t} := by simpa using hT64.2 {t} (by decide)")
        L.append(f"  have hTa : s.mem.accessible {A64 + 8*t} 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)")
        extra = ", hTv"
    else:
        i = t - 20
        A = ABIG + 32*i
        L.append(f"  have hTv : s.mem.readLE {A} 32 = {10**t} := by simpa using hTB.2 {i} (by decide)")
        L.append(f"  have hTa : s.mem.accessible {A} 32 false = true := Memory.accessible_mono _ hTB.1 (by omega) (by omega)")
        c = [(10**t >> (64*j)) % 2**64 for j in range(4)]
        L.append(f"  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem {A} {c[0]} {c[1]} {c[2]} {c[3]} (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)")
        for j in range(1, 4):
            L.append(f"  have hT{j} : s.mem.readLE {A + 8*j} 8 = {c[j]} := hT{j}'")
        extra = ""
    L.append(f"  janus_run [hc{extra}{zs(k)}]")
    if t < 20 or b <= 64:
        for j in range(4):
            L.append(f"  have := Util.readLE8_lt s.mem {xa(j)}")
        L.append("  all_goals omega")
    else:
        L.append("  all_goals (")
        for j in range(4):
            L.append(f"    have := Util.readLE8_lt s.mem {xa(j)}")
        L.append("    simp only [Janus.Tactic.sub_flags_c, Janus.Tactic.awc_fst_toNat, Util.awc_c_dec, Util.dec_ite, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.zero_add] at hbr")
        L.append("    repeat' split at hbr")
        L.append("    all_goals omega)")
    return "\n".join(L)
os.makedirs(ROOT + '/lean/Fv256/Arm64/L10Cases', exist_ok=True)
for (k, m) in cases:
    open(ROOT + f'/lean/Fv256/Arm64/L10Cases/C{k}_{m}.lean', 'w').write(
        HDR + OPEN + "namespace Fv256.Arm64.Log10\n\n" + case(k, m) + "\n\nend Fv256.Arm64.Log10\n")
