#!/usr/bin/env python3
"""g4w.py: weights of the inputs of a chain of units w.r.t. a set of output vars (weighted by 64-bit limbs): returns {var: exponent or None}"""
import sys, random, os
sys.path.insert(0, os.path.dirname(__file__))
import g4sim, g4seg as g
def weights(cuts, outs, modexp=320):
    _, n0 = g.Ldef(cuts[0]); M64 = 1 << 64; T = 1 << modexp
    def B(env):
        e = g4sim.run(cuts, env)
        return sum(e[o] << (64 * i) for i, o in enumerate(outs))
    base = {n: random.randrange(M64 >> 2) for n in n0}
    b0 = B(base); w = {}
    for n in n0:
        e = dict(base); e[n] += 1
        d = (B(e) - b0) % T
        w[n] = None if d == 0 else (d.bit_length() - 1 if d & (d - 1) == 0 else ('?', d))
    return w
if __name__ == '__main__':
    cuts = [int(x, 16) for x in sys.argv[1].split(',')]
    outs = sys.argv[2].split(',')
    for k, v in weights(cuts, outs).items(): print(k, v)
