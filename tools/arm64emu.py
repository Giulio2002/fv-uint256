#!/usr/bin/env python3
"""arm64emu.py: python emulator for the Reciprocal arm64 body (b8e08..b94fc), used to name values at cut points.
usage: from arm64emu import run; trace = run(m) -> dict addr -> (regs, mem, flags) BEFORE executing the instruction at addr"""
import re, sys, os
sys.path.insert(0, os.path.dirname(__file__))
from arm64live import parse
M = (1 << 64) - 1
def val(r, regs):
    r = r.strip()
    if r in ('xzr', 'wzr'): return 0
    if r == 'sp': return regs['sp']
    m = re.fullmatch(r'([xw])(\d+)', r)
    v = regs.get(int(m.group(2)), 0)
    return v & 0xffffffff if m.group(1) == 'w' else v
def run(m, dis='/srv/fv-uint256-wBm/build/recip-arm64.dis'):
    ins = parse(dis); byaddr = {a: (k, i) for k, i in enumerate(ins) for a in [i[0]]}
    L = 3 + 0; s = 64 - m.bit_length() if False else 256 - m.bit_length()
    y = (m << s) & ((1 << 256) - 1)
    regs = {'sp': 0x1000}
    mem = {}
    for i in range(4): mem[0x1000 + 32 + 8 * i] = (y >> (64 * i)) & M
    mem[0x1000 + 176] = 255 - s
    # x0 holds pointer-to-m in the prologue; here x0 is overwritten by the first stage-1 instructions
    flags = dict(n=0, z=0, c=0, v=0)
    pc = 0xb8e08; trace = {}
    def setf(a, b, res, sub, cin):
        pass
    while pc != 0xb94fc:
        k, (addr, mn, ops) = byaddr[pc]
        trace[pc] = (dict(regs), dict(mem), dict(flags))
        parts = [p.strip() for p in re.split(r',\s*(?![^\[]*\])', ops)]
        def w(reg, v):
            reg = reg.strip()
            if reg in ('xzr', 'wzr'): return
            n = int(reg[1:]); regs[n] = v & (M if reg[0] == 'x' else 0xffffffff)
        def imm(t):
            t = t.strip().lstrip('#'); return int(t, 0)
        def opnd(t):
            t = t.strip()
            if t.startswith('#'): return imm(t) & M
            return val(t, regs)
        def shifted(ps):
            v = opnd(ps[0])
            if len(ps) > 1:
                m_ = re.match(r'(lsl|lsr) #(\d+)', ps[1])
                if m_: v = (v << int(m_.group(2))) & M if m_.group(1) == 'lsl' else v >> int(m_.group(2))
            return v
        nxt = pc + 4
        def addf(a, b, c):
            r = a + b + c; res = r & M
            flags.update(n=res >> 63, z=int(res == 0), c=int(r > M), v=int(((a ^ res) & (b ^ res)) >> 63))
            return res
        def subf(a, b, c):  # a - b - (1-c)
            r = a + ((~b) & M) + c; res = r & M
            flags.update(n=res >> 63, z=int(res == 0), c=int(r > M), v=int(((a ^ b) & (a ^ res)) >> 63))
            return res
        if mn == 'mov': w(parts[0], opnd(parts[1]))
        elif mn == 'orr': w(parts[0], opnd(parts[1]) | shifted(parts[2:]))
        elif mn == 'and': w(parts[0], opnd(parts[1]) & shifted(parts[2:]))
        elif mn == 'add': w(parts[0], (opnd(parts[1]) + shifted(parts[2:])) & M)
        elif mn == 'sub': w(parts[0], (opnd(parts[1]) - shifted(parts[2:])) & M)
        elif mn == 'adds': w(parts[0], addf(opnd(parts[1]), shifted(parts[2:]), 0))
        elif mn == 'adcs': w(parts[0], addf(opnd(parts[1]), opnd(parts[2]), flags['c']))
        elif mn == 'adc': w(parts[0], (opnd(parts[1]) + opnd(parts[2]) + flags['c']) & M)
        elif mn == 'subs': w(parts[0], subf(opnd(parts[1]), shifted(parts[2:]), 1))
        elif mn == 'sbcs': w(parts[0], subf(opnd(parts[1]), opnd(parts[2]), flags['c']))
        elif mn == 'ngc': w(parts[0], (0 - opnd(parts[1]) - (1 - flags['c'])) & M)
        elif mn == 'neg': w(parts[0], (-opnd(parts[1])) & M)
        elif mn == 'cmp':
            if parts[0][0] == 'w': subf(opnd(parts[0]) & 0xffffffff, opnd(parts[1]) & 0xffffffff, 1) if False else None
            if parts[0][0] == 'w':
                a, b = val(parts[0], regs), opnd(parts[1]) & 0xffffffff; r = a + ((~b) & 0xffffffff) + 1
                flags.update(n=(r >> 31) & 1, z=int((r & 0xffffffff) == 0), c=int(r > 0xffffffff), v=0)
            else: subf(opnd(parts[0]), opnd(parts[1]), 1)
        elif mn == 'mul': w(parts[0], (opnd(parts[1]) * opnd(parts[2])) & M)
        elif mn == 'umulh': w(parts[0], (opnd(parts[1]) * opnd(parts[2])) >> 64)
        elif mn == 'udiv': w(parts[0], opnd(parts[1]) // opnd(parts[2]))
        elif mn == 'lsr': w(parts[0], opnd(parts[1]) >> (opnd(parts[2]) & 63) if not parts[2].startswith('#') else opnd(parts[1]) >> imm(parts[2]))
        elif mn == 'lsl': w(parts[0], (opnd(parts[1]) << (opnd(parts[2]) & 63)) & M if not parts[2].startswith('#') else (opnd(parts[1]) << imm(parts[2])) & M)
        elif mn == 'csel':
            cc = parts[3]
            cond = {'eq': flags['z'] == 1, 'ne': flags['z'] == 0, 'lt': flags['n'] != flags['v'], 'ge': flags['n'] == flags['v'],
                    'gt': flags['z'] == 0 and flags['n'] == flags['v'], 'cc': flags['c'] == 0}[cc]
            w(parts[0], opnd(parts[1]) if cond else opnd(parts[2]))
        elif mn in ('ldr', 'ldp', 'str', 'stp'):
            mo = re.search(r'\[(\w+)(?:, #(-?\w+))?\]', ops); base = mo.group(1); off = int(mo.group(2), 0) if mo.group(2) else 0
            a = val(base, regs) + off if base != 'sp' else regs['sp'] + off
            rs = [p for p in parts[:-1] if not p.startswith('[')] if mn in ('ldp', 'stp') else [parts[0]]
            if mn == 'ldr': w(rs[0], mem.get(a, 0))
            elif mn == 'ldp': w(rs[0], mem.get(a, 0)); w(rs[1], mem.get(a + 8, 0))
            elif mn == 'str': mem[a] = opnd(rs[0])
            else: mem[a] = opnd(rs[0]); mem[a + 8] = opnd(rs[1])
        elif mn == 'nop': pass
        elif mn == 'b': nxt = int(re.search(r'0x([0-9a-f]+)', ops).group(1), 16)
        elif mn.startswith('b.') or mn in ('cbz', 'cbnz'):
            tgt = int(re.search(r'0x([0-9a-f]+)', ops).group(1), 16)
            if mn == 'cbz': take = opnd(parts[0]) == 0
            elif mn == 'cbnz': take = opnd(parts[0]) != 0
            else:
                cc = mn[2:]; take = {'ne': flags['z'] == 0, 'eq': flags['z'] == 1, 'ls': not (flags['c'] == 1 and flags['z'] == 0)}[cc]
            if take: nxt = tgt
        else: raise Exception('unhandled ' + mn + ' ' + ops)
        pc = nxt
    trace[pc] = (dict(regs), dict(mem), dict(flags))
    return trace
if __name__ == '__main__':
    sys.path.insert(0, '/srv/fv-uint256-wBm/wip-b4')
    import random
    import model as MD
    random.seed(3)
    for _ in range(5):
        bits = random.randint(194, 256); m = random.getrandbits(bits) | (1 << (bits - 1)) | 1
        t = run(m); r, mem, fl = t[0xb94fc]
        mu = sum(mem[0x1000 + 280 + 8 * i] << (64 * i) for i in range(5))
        print(hex(m)[:12], mu == MD.model(m))
