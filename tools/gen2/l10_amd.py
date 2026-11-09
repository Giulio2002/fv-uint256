#!/usr/bin/env python3 -I
# l10_amd.py [k:m ...] : writes lean/Fv256/Proofs/Amd64/L10Cases/C<k>_<m>.lean (one module per top nonzero limb k and its bit length m) and Zero.lean
import os, re, sys
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
def _addr(sym):
    t = open(os.environ.get('L10_EXTRACTED', ROOT + '/build/ex-amd64-Log10/Extracted.lean')).read()
    return int(re.search(r'def dataAddr\.«github\.com/holiman/uint256\.' + sym + r'» : Nat := (0x[0-9a-f]+|\d+)', t).group(1), 0)
A64, ABIG = _addr('pows64'), _addr('pows')
args = sys.argv[1:]
cases = [tuple(map(int, a.split(':'))) for a in args] or [(k, m) for k in range(4) for m in range(1, 65)]
HDR = "import Extracted\nimport Fv256.Spec\nimport Fv256.Util\nimport Fv256.Amd64.L10Defs\n"
OPEN = "\nopen Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic\n\n"
def tval(b): return (1233 * b + 1233) >> 12
def xa(j): return '(x.toNat + %d)' % (8*j) if j else 'x.toNat'
def limbs(k, m):
    L = []
    for j in range(3, -1, -1):
        a = f"s.mem.readLE {xa(j)} 8"
        if j > k: L.append(f"{a} = 0")
        elif j == k: L.append(f"2 ^ {m-1} ≤ {a} ∧ {a} < 2 ^ {m}")
    return " ∧ ".join(L)
PRE = """(fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB)"""
def pat(k):
    return ', '.join([f'hz{j}' for j in range(3, k, -1)] + ['hl1', 'hl2'])
def zs(k): return ''.join(f', hz{j}' for j in range(3, k, -1))
def hw(name, addr):
    return (f"  have {name} : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE {addr} 8) = s.mem.readLE {addr} 8 := fun v => by\n"
            "    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]\n")
COMMON = ("  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, %s⟩\n"
          "  janus64_intro hs\n"
          "  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB\n"
          "  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB\n")
WR = ("  have hwr : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (s.regs 4).toNat 8) = s.mem.readLE (s.regs 4).toNat 8 := fun v => by\n"
      "    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]\n")
WX = "".join(hw(f"hw{j}", xa(j)) for j in range(4))
def case(k, m):
    b = 64 * k + m; t = tval(b)
    top = f"s.mem.readLE {xa(k)} 8"
    L = ["set_option maxHeartbeats 64000000 in", f"theorem c{k}_{m} (x : BitVec 64) :",
         "    Ensures Extracted.program Extracted.entry [x]", "      " + PRE + " ∧\n        " + limbs(k, m) + ")",
         "      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by"]
    body = COMMON % pat(k)
    body += f"  have hc : Janus.Arm64.clzNat 64 ({top}) = {64-m} := by\n"
    body += f"    have := Util.clz_bl 64 ({top}) (Util.readLE8_lt s.mem _)\n"
    body += f"    have h2 : Spec.bitLen ({top}) = {m} := Util.bitLen_of_range _ {m} (by omega) (by omega) (by omega)\n    omega\n"
    body += WR + WX
    extra = ""
    def tvar(name, addr, val):
        r = (f"  obtain ⟨{name}, hE{name}⟩ : ∃ T, s.mem.readLE {addr} 8 = T := ⟨_, rfl⟩\n"
             f"  have hV{name} : {name} = {val} := by rw [← hE{name}]; exact @@HT@@\n"
             f"  have hB{name} : {name} < 18446744073709551616 := by rw [hV{name}]; decide\n"
             f"  have hw{name} : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE {addr} 8) = {name} := fun v => by\n"
             f"    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE{name}\n")
        return r
    if t < 20:
        a = A64 + 8*t
        body += f"  have hTv : s.mem.readLE {a} 8 = {10**t} := by simpa using hT64.2 {t} (by decide)\n"
        body += f"  have hTa : s.mem.accessible {a} 8 false = true := Janus.Arm64.Memory.accessible_mono _ hT64.1 (by omega) (by omega)\n"
        body += tvar("T", a, 10**t).replace("@@HT@@", "hTv")
        extra = ", hwT"
    else:
        i = t - 20; A = ABIG + 32*i
        c = [(10**t >> (64*j)) % 2**64 for j in range(4)]
        body += f"  have hTv : s.mem.readLE {A} 32 = {10**t} := by simpa using hTB.2 {i} (by decide)\n"
        body += f"  have hTa : s.mem.accessible {A} 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)\n"
        for j in range(4): body += f"  have hl{j} := Util.readLE8_lt s.mem {A + 8*j}\n"
        body += f"  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem {A} {c[0]} {c[1]} {c[2]} {c[3]} (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)\n"
        for j in range(1, 4): body += f"  have hT{j} : s.mem.readLE {A + 8*j} 8 = {c[j]} := hT{j}'\n"
        for j in range(4):
            body += tvar(f"T{j}", A + 8*j, c[j]).replace("@@HT@@", f"hT{j}")
        extra = ", hwT0, hwT1, hwT2, hwT3"
    body += "".join(f"  have b{j} := Util.readLE8_lt s.mem {xa(j)}\n" for j in range(4))
    body += f"  have hne : s.mem.readLE {xa(k)} 8 ≠ 0 := by omega\n"
    body += f"  janus64_run [Util.cmp_eq_mod, hne, hwr, hc{extra}{zs(k)}, hw0, hw1, hw2, hw3]\n"
    if t < 20 or b <= 64:
        body += "  all_goals (simp only [valueAt, Util.readLE_32]; omega)\n"
    else:
        body += "  all_goals (\n    simp only [valueAt, Util.readLE_32]\n    (try simp only [Util.dec_ite] at hbr)\n    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)\n"
    return "\n".join(L) + " := by\n".replace(" := by\n", "\n") + body if False else "\n".join(L) + "\n" + body
os.makedirs(ROOT + '/lean/Fv256/Proofs/Amd64/L10Cases', exist_ok=True)
for (k, m) in cases:
    open(ROOT + f'/lean/Fv256/Proofs/Amd64/L10Cases/C{k}_{m}.lean', 'w').write(
        HDR + OPEN + "namespace Fv256.Amd64.Log10\n\n" + case(k, m) + "\nend Fv256.Amd64.Log10\n")
