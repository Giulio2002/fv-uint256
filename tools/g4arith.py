#!/usr/bin/env python3
"""g4arith.py: build a pure-Nat arithmetic lemma for a chain of generated segment units.
usage in python: arith(cuts, name, concl, extra_hyps='') -> Lean text.  `concl` uses names of cut Z (x47frbx ...) and cut A (x2f8rax ...)."""
import re, sys, os
sys.path.insert(0, os.path.dirname(__file__))
import g4chain, g4seg as g
def chain_data(cuts):
    units = [g4chain.load(a, b) for a, b in zip(cuts, cuts[1:])]
    for k in range(1, len(units)):
        u = units[k]; actual = units[k - 1]['outargs']
        mp = dict(zip(u['invars'], actual))
        sub = lambda s: re.sub(r'\bx[0-9a-f]+[a-z0-9]+\b', lambda m: mp.get(m.group(0), m.group(0)), s)
        u['eqs'] = [(n, sub(e)) for n, e in u['eqs']]
        u['outargs'] = [mp.get(a, a) for a in u['outargs']]
    A, Z = cuts[0], cuts[-1]
    invars = units[0]['invars']
    alleqs = []
    for u in units: alleqs += u['eqs']
    _, namesZ = g.Ldef(Z)
    res = dict(zip(namesZ, units[-1]['outargs']))
    return invars, alleqs, res
def arith(cuts, name, concl, tactic='omega', extra=''):
    invars, eqs, res = chain_data(cuts)
    sub = lambda s: re.sub(r'\bx[0-9a-f]+[a-z0-9]+\b', lambda m: res.get(m.group(0), m.group(0)), s)
    new = [n for n, e in eqs]
    out = 'theorem %s ' % name
    allv = invars + [n for n in new if n not in invars]
    out += '(%s : Nat)\n' % ' '.join(allv)
    for v in invars: out += '    (b_%s : %s < 2 ^ 64)\n' % (v, v)
    for n, e in eqs: out += '    (h_%s : %s = %s)\n' % (n, n, e)
    out += '    %s: %s := by\n  %s\n' % (extra, sub(concl), tactic)
    return out

def adc_lemma(cuts, name, outs, modexp=320, tactic='omega', timeout_note=''):
    import g4w
    w = g4w.weights(cuts, outs, modexp)
    lhs = ' + '.join(('2 ^ %d * %s' % (64 * 0, o)) if False else (o if i == 0 else '2 ^ %d * %s' % (64 * i, o)) for i, o in enumerate(outs))
    terms = []
    for v, e in w.items():
        if e is None: continue
        assert isinstance(e, int), (v, e)
        terms.append(v if e == 0 else '2 ^ %d * %s' % (e, v))
    rhs = '(%s) %% 2 ^ %d' % (' + '.join(terms), modexp)
    return arith(cuts, name, '%s = %s' % (lhs, rhs), tactic=tactic)

def unit_chain(cuts, name, outs, modexp=320, tactic='omega', final_w=None):
    """Per-unit invariant lemmas + chain theorem.  Functional at the last cut: sum 2^(64 i) * outs[i] (or final_w dict).
    Returns Lean text."""
    import g4w
    units = [g4chain.load(a, b) for a, b in zip(cuts, cuts[1:])]
    # actual names
    inact = [units[0]['invars']]
    for k in range(1, len(units)):
        u = units[k]; actual = units[k - 1]['outargs']
        mp = dict(zip(u['invars'], actual))
        sub = lambda s, mp=mp: re.sub(r'\bx[0-9a-f]+[a-z0-9]+\b', lambda m: mp.get(m.group(0), m.group(0)), s)
        u['eqs'] = [(n, sub(e)) for n, e in u['eqs']]
        u['outargs'] = [mp.get(a, a) for a in u['outargs']]
        inact.append(actual)
    # weights per cut (local names of that cut)
    W = []
    for k in range(len(units)):
        W.append(g4w.weights(cuts[k:], outs, modexp))
    _, nZ = g.Ldef(cuts[-1])
    Wlast = {n: 64 * i for i, o in enumerate(outs) for n in [o]}
    text = ''
    T = 2 ** modexp
    for k, u in enumerate(units):
        a, b = cuts[k], cuts[k + 1]
        _, nA = g.Ldef(a); _, nB = g.Ldef(b)
        in_act = inact[k]
        wA = W[k]
        lhs_terms = [(in_act[i], wA[nA[i]]) for i in range(len(nA)) if wA[nA[i]] is not None]
        out_act = u['outargs']
        if k + 1 < len(units): wB = W[k + 1]
        else: wB = {o: 64 * i for i, o in enumerate(outs)}
        rhs_terms = [(out_act[i], wB.get(nB[i])) for i in range(len(nB)) if wB.get(nB[i]) is not None]
        for _, e in lhs_terms + rhs_terms: assert isinstance(e, int), e
        fmt = lambda ts: ' + '.join(v if e == 0 else '2 ^ %d * %s' % (e, v) for v, e in ts) or '0'
        newv = [n for n, e in u['eqs']]
        allv = list(dict.fromkeys(in_act + newv + [v for v, _ in rhs_terms]))
        th = 'theorem %s_u%d ' % (name, k) + '(%s : Nat)\n' % ' '.join(allv)
        for v in in_act: th += '    (b_%s : %s < 2 ^ 64)\n' % (v, v)
        for n, e in u['eqs']: th += '    (h_%s : %s = %s)\n' % (n, n, e)
        th += '    : (%s) %% 2 ^ %d = (%s) %% 2 ^ %d := by\n  %s\n\n' % (fmt(lhs_terms), modexp, fmt(rhs_terms), modexp, tactic)
        u['th'] = th; u['lname'] = '%s_u%d' % (name, k); u['in_act'] = in_act; u['allv'] = allv; u['lhs'] = fmt(lhs_terms); u['rhs'] = fmt(rhs_terms)
        text += th
    return text, units, inact, W

def prod_units(cuts, name, wlast, qs, ms, modexp=320, tactic='omega'):
    """product stage: per-unit lemmas Psi_k(in) = Psi_{k+1}(out) mod 2^modexp where Psi = weighted live words + pending products.
    wlast: {local name at last cut: exponent}; qs, ms: lists of the q_i / m_j names (cut-0 names)."""
    units = [g4chain.load(a, b) for a, b in zip(cuts, cuts[1:])]
    inact = [units[0]['invars']]
    for k in range(1, len(units)):
        u = units[k]; actual = units[k - 1]['outargs']
        mp = dict(zip(u['invars'], actual))
        sub = lambda s, mp=mp: re.sub(r'\bx[0-9a-f]+[a-z0-9]+\b', lambda m: mp.get(m.group(0), m.group(0)), s)
        u['eqs'] = [(n, sub(e)) for n, e in u['eqs']]
        u['outargs'] = [mp.get(a, a) for a in u['outargs']]
        inact.append(actual)
    nu = len(units)
    _, nZ = g.Ldef(cuts[-1])
    outl = [units[-1]['outargs']]
    # omega per cut (actual names)
    omega = [None] * (nu + 1)
    omega[nu] = {units[-1]['outargs'][i]: [wlast[nZ[i]]] for i in range(len(nZ)) if wlast.get(nZ[i]) is not None}
    for k in range(nu - 1, -1, -1):
        outs = set(units[k]['outargs'])
        omega[k] = {}
        for v in inact[k]:
            tot = list(omega[k + 1].get(v, [])) if v in outs else []
            for n, e in units[k]['eqs']:
                if e.strip() == v + ' % 18446744073709551616' and n in outs: tot += omega[k + 1].get(n, [])
            if tot: omega[k][v] = tot
    # pending products per cut
    atoms = [set() for _ in range(nu + 1)]
    for k in range(nu - 1, -1, -1):
        atoms[k] = set(atoms[k + 1])
        for n, e in units[k]['eqs']:
            for a, b in re.findall(r'(x[0-9a-f]+[a-z0-9]+) \* (x[0-9a-f]+[a-z0-9]+)', e): atoms[k].add((a, b))
    alias = {}
    for u in units:
        for n, e in u['eqs']:
            mm = re.fullmatch(r'(x[0-9a-f]+[a-z0-9]+) % 18446744073709551616', e.strip())
            if mm: alias[n] = alias.get(mm.group(1), mm.group(1))
    def pairw(a, b):
        a = alias.get(a, a); b = alias.get(b, b)
        for x, y in ((a, b), (b, a)):
            if x in ms and y in qs: return 64 * (ms.index(x) + qs.index(y))
        raise Exception('pair %s %s' % (a, b))
    mulb = ''
    text = ''; T = 2 ** modexp
    for k, u in enumerate(units):
        def psi(k):
            ts = [(v, e) for v, es in omega[k].items() for e in es]
            s = ' + '.join(v if e == 0 else '2 ^ %d * %s' % (e, v) for v, e in ts)
            pr = ' + '.join('2 ^ %d * (%s * %s)' % (pairw(a, b), a, b) for a, b in sorted(atoms[k]))
            return ' + '.join(x for x in (s, pr) if x) or '0'
        in_act = inact[k]; out_act = u['outargs']
        newv = [n for n, e in u['eqs']]
        allv = list(dict.fromkeys(in_act + newv + out_act))
        th = 'theorem %s_u%d ' % (name, k) + '(%s : Nat)\n' % ' '.join(allv)
        for v in in_act: th += '    (b_%s : %s < 2 ^ 64)\n' % (v, v)
        for n, e in u['eqs']: th += '    (h_%s : %s = %s)\n' % (n, n, e)
        th += '    : (%s) %% 2 ^ %d = (%s) %% 2 ^ %d := by\n' % (psi(k), modexp, psi(k + 1), modexp)
        # product bounds and commutations for atoms present in this unit's eqs
        pr = sorted({(a, b) for n, e in u['eqs'] for a, b in re.findall(r'(x[0-9a-f]+[a-z0-9]+) \* (x[0-9a-f]+[a-z0-9]+)', e)} | atoms[k + 1] | atoms[k])
        for a, b in pr:
            if a in in_act and b in in_act:
                th += '  have := mulb %s %s b_%s b_%s\n' % (a, b, a, b)
            th += '  have := Nat.mul_comm %s %s\n' % (a, b)
        for n, e in u['eqs']:
            mm = re.fullmatch(r'(x[0-9a-f]+[a-z0-9]+) % 18446744073709551616', e.strip())
            if mm and mm.group(1) in in_act:
                th += '  have e_%s : %s = %s := by rw [h_%s]; exact (Nat.mod_eq_of_lt b_%s).symm\n  subst e_%s\n' % (n, mm.group(1), n, n, mm.group(1), n)
        th += '  %s\n\n' % tactic
        u['allv'] = allv; u['in_act'] = in_act; u['lname'] = '%s_u%d' % (name, k)
        text += th
    return text, units, inact, omega

def bounded_units(cuts, name, finalw, dropexp=256, tactic='omega'):
    """integer-weight invariants with a dropped column: per unit Psi_{k+1}(out) <= Psi_k(in) < Psi_{k+1}(out) + 2^320 (or exact =)."""
    import g4w2, g4sim, random
    om = g4w2.weights_chain(cuts, finalw, dropexp)
    units = [g4chain.load(a, b) for a, b in zip(cuts, cuts[1:])]
    inact = [units[0]['invars']]
    for k in range(1, len(units)):
        u = units[k]; actual = units[k - 1]['outargs']
        mp = dict(zip(u['invars'], actual))
        sub = lambda s, mp=mp: re.sub(r'\bx[0-9a-f]+[a-z0-9]+\b', lambda m: mp.get(m.group(0), m.group(0)), s)
        u['eqs'] = [(n, sub(e)) for n, e in u['eqs']]
        u['outargs'] = [mp.get(a, a) for a in u['outargs']]
        inact.append(actual)
    names = [g.Ldef(c)[1] for c in cuts]
    # exactness test
    M64 = 1 << 64
    exact = [True] * len(units)
    for t in range(200):
        env = {n: random.randrange(M64) for n in names[0]}
        envs = [env]
        for k in range(len(units)): envs.append(g4sim.step(envs[-1], cuts[k], cuts[k + 1]))
        psi = [sum(om[k].get(n, 0) * v for n, v in envs[k].items()) for k in range(len(cuts))]
        for k in range(len(units)):
            d = psi[k] - psi[k + 1]
            assert 0 <= d < 2 ** 320, (k, d)
            if d != 0: exact[k] = False
    def term(v, w):
        e = w.bit_length() - 1
        assert w == 1 << e, w
        return v if e == 0 else '2 ^ %d * %s' % (e, v)
    text = ''
    for k, u in enumerate(units):
        nA = names[k]; nB = names[k + 1]
        in_act = inact[k]; out_act = u['outargs']
        lhs = ' + '.join(term(in_act[i], om[k][nA[i]]) for i in range(len(nA)) if nA[i] in om[k]) or '0'
        rhs = ' + '.join(term(out_act[i], om[k + 1][nB[i]]) for i in range(len(nB)) if nB[i] in om[k + 1]) or '0'
        newv = [n for n, e in u['eqs']]
        allv = list(dict.fromkeys(in_act + newv + out_act))
        th = 'theorem %s_u%d ' % (name, k) + '(%s : Nat)\n' % ' '.join(allv)
        for v in in_act: th += '    (b_%s : %s < 2 ^ 64)\n' % (v, v)
        for n, e in u['eqs']: th += '    (h_%s : %s = %s)\n' % (n, n, e)
        import g4anf
        pf = '\n'.join(g4anf.anf([e for n, e in u['eqs']], 'a%d' % k)) + '\n  ' + tactic
        if exact[k]: th += '    : %s = %s := by\n%s\n\n' % (lhs, rhs, pf)
        else: th += '    : (%s) ≤ (%s) ∧ (%s) < (%s) + 2 ^ 320 := by\n%s\n\n' % (rhs, lhs, lhs, rhs, pf)
        u['allv'] = allv; u['in_act'] = in_act; u['lname'] = '%s_u%d' % (name, k); u['exact'] = exact[k]; u['lhs'] = lhs; u['rhs'] = rhs
        text += th
    return text, units, inact, om, exact
