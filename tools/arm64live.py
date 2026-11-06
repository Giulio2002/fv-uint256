#!/usr/bin/env python3
"""arm64live.py: tiny aarch64 liveness for the Reciprocal arm64 disassembly (build/recip-arm64.dis, objdump -D -b binary).
usage: arm64live.py DIS [ADDR ...]   -> prints live regs / sp-slots / flags before each ADDR (hex)  (all straight-line + forward branches)
Slots are [sp,#d] 8-byte words. Memory through other bases is ignored except the known Lsh output (sp+0x20..0x3f, defined by `bl`).
At `ret` the result words sp+280..312 are live; panics end the path (nothing live)."""
import re, sys
def parse(path):
    ins = []
    for ln in open(path):
        m = re.match(r'\s*([0-9a-f]+):\t([0-9a-f ]+)\t(\S+)\s*(.*)', ln)
        if m:
            ops = m.group(4).split('//')[0].strip()
            ins.append((int(m.group(1), 16), m.group(3), ops))
    return ins
def regs_in(op):
    return [('x%s' % m.group(1)) for m in re.finditer(r'\b[xw](\d+)\b', op)]
FLAGW = {'adds', 'subs', 'adcs', 'sbcs', 'cmp', 'cmn', 'negs', 'ngcs', 'tst', 'ands'}
FLAGR = {'adc', 'adcs', 'sbc', 'sbcs', 'ngc', 'ngcs', 'csel', 'csinc', 'csinv', 'csneg', 'cset', 'csetm'}
def memop(op):
    m = re.search(r'\[(\w+)(?:, #(-?\w+))?\]', op)
    if not m: return None
    return m.group(1), int(m.group(2), 0) if m.group(2) else 0
def du(i):
    addr, mn, ops = i
    defs, uses, mdef, muse = set(), set(), set(), set()
    fd = mn in FLAGW; fu = mn in FLAGR or (mn.startswith('b.'))
    parts = [p.strip() for p in re.split(r',\s*(?![^\[]*\])', ops)] if ops else []
    allregs = regs_in(ops)
    if mn in ('str', 'stp', 'strb', 'strh'):
        mo = memop(ops)
        src = regs_in(ops.split('[')[0])
        uses |= set(src)
        if mo:
            b, off = mo
            if b == 'sp': 
                for k in range(len(src)): mdef.add(off + 8 * k)
            else: uses.add('x' + b[1:]) if b[0] in 'xw' else None
    elif mn in ('ldr', 'ldp', 'ldrb', 'ldrh'):
        mo = memop(ops)
        dst = regs_in(ops.split('[')[0])
        defs |= set(dst)
        if mo:
            b, off = mo
            if b == 'sp':
                for k in range(len(dst)): muse.add(off + 8 * k)
            elif b[0] in 'xw': uses.add('x' + b[1:])
    elif mn in ('cbz', 'cbnz'):
        uses |= set(allregs)
    elif mn in ('b', 'ret', 'nop'): pass
    elif mn == 'bl':
        defs |= {'x%d' % k for k in range(0, 16)}; uses |= {'x0', 'x1', 'x2'}
        for k in range(0x20, 0x40, 8): mdef.add(k)
    elif mn in ('cmp', 'cmn', 'tst'):
        uses |= set(allregs)
    else:
        if allregs:
            d = regs_in(parts[0]); defs |= set(d)
            uses |= set(allregs[len(d):]) if True else set()
            # reg operands after the first are uses; also first if it's a read-modify (none here)
    defs.discard('x31'); uses.discard('x31')
    if 'sp' in ops.replace('[sp', '') : pass
    return defs, uses, mdef, muse, fd, fu
def successors(ins, idx):
    addr, mn, ops = ins[idx]
    nxt = idx + 1 if idx + 1 < len(ins) else None
    if mn == 'ret': return []
    m = re.search(r'0x([0-9a-f]+)', ops)
    tgt = None
    if m and (mn == 'b' or mn.startswith('b.') or mn in ('cbz', 'cbnz')):
        t = int(m.group(1), 16)
        for k, x in enumerate(ins):
            if x[0] == t: tgt = k
    if tgt is not None and ins[tgt][0] >= 0xb9534: tgt = None   # panic/morestack stubs: infeasible paths, nothing live
    if mn == 'b': return [tgt] if tgt is not None else []
    if mn == 'bl':
        t = int(m.group(1), 16) if m else 0
        return [nxt] if t in (0xbcbf0,) and nxt is not None else []   # panic stubs do not return
    if mn.startswith('b.') or mn in ('cbz', 'cbnz'):
        return [x for x in (nxt, tgt) if x is not None]
    return [nxt] if nxt is not None else []
def analyse(ins):
    n = len(ins)
    LR = [set() for _ in range(n)]; LM = [set() for _ in range(n)]; LF = [False] * n
    dus = [du(i) for i in ins]
    changed = True
    while changed:
        changed = False
        for idx in range(n - 1, -1, -1):
            addr, mn, ops = ins[idx]
            defs, uses, mdef, muse, fd, fu = dus[idx]
            outR, outM, outF = set(), set(), False
            if mn == 'ret':
                outM = {280, 288, 296, 304, 312}
            for s in successors(ins, idx):
                outR |= LR[s]; outM |= LM[s]; outF |= LF[s]
            inR = (outR - defs) | uses
            inM = (outM - mdef) | muse
            inF = (outF and not fd) or fu
            if inR != LR[idx] or inM != LM[idx] or inF != LF[idx]:
                LR[idx], LM[idx], LF[idx] = inR, inM, inF; changed = True
    return LR, LM, LF
if __name__ == '__main__':
    ins = parse(sys.argv[1])
    LR, LM, LF = analyse(ins)
    want = [int(a, 16) for a in sys.argv[2:]]
    for k, i in enumerate(ins):
        if (not want and i[0] >= 0xb8e08) or i[0] in want:
            if not want and LF[k]: continue
            print('%x %-6s %s | regs %s | slots %s | flags %s' % (i[0], i[1], i[2][:30],
                  ' '.join(sorted(LR[k], key=lambda r: int(r[1:]))), ' '.join(str(s) for s in sorted(LM[k])), LF[k]))
