import re, sys, os
sys.path.insert(0, os.path.dirname(__file__))
import g4seg as g
def hi_names(cut=0x1cd):
    t = open(g.ROOT + '/lean/Fv256/Amd64/ReduceSegA.lean').read()
    i = t.index('def PostA'); j = t.index('theorem segA ', i); d = t[i:j]
    body = d[d.index('∃ '):]
    rest = body[2:].split(', ', 1)[1]
    cs = []; depth = 0; cur = ''; k = 0
    while k < len(rest):
        c = rest[k]
        if c == '(': depth += 1
        if c == ')': depth -= 1
        if depth == 0 and rest.startswith(' ∧ ', k): cs.append(cur.strip()); cur = ''; k += 3; continue
        cur += c; k += 1
    cs.append(cur.strip())
    defs = {}; regmap = {}; memmap = {}
    for f in cs:
        m = re.fullmatch(r"\((v\d+) = (.*)\)", f)
        if m: defs[m.group(1)] = m.group(2)
        m = re.fullmatch(r"\(S'\.regs (\d+) = BitVec\.ofNat 64 (v\d+)\)", f)
        if m: regmap[int(m.group(1))] = m.group(2)
        m = re.fullmatch(r"\(S'\.mem\.readLE \(BitVec\.toNat \(s\.regs 4\) (-|\+) (\d+)\) 8 = (v\d+) % 2 \^ 64\)", f)
        if m: memmap[(-1 if m.group(1) == '-' else 1) * int(m.group(2))] = m.group(3)
    its = g.items(cut); _, names = g.Ldef(cut)
    out = {}
    for (k, key), nm in zip(its, names):
        v = regmap[g.RIDX[key]] if k == 'r' else memmap[key - 288]
        out[nm] = (v, defs[v])
    return out
if __name__ == '__main__':
    for n, (v, e) in hi_names().items(): print(n, v, 'HI' if e.endswith('/ 18446744073709551616') else ('PROD' if '*' in e else 'LIMB'))
