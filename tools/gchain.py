#!/usr/bin/env python3
"""gchain.py NAME  c0 c1 ... ck : compose consecutive generated segments/chains (cut addresses hex) into one chain unit.
Units are files lean/Fv256/Amd64/RecipG/<kind>_A_B.lean (g = segment, c = chain) defining P*_A_B and theorem g_/c_A_B."""
import re, sys, os, subprocess
sys.path.insert(0, os.path.dirname(__file__))
import gseg
ROOT = gseg.ROOT
D = ROOT + '/lean/Fv256/Amd64/RecipG/'
def load(A, B):
    for kind in ('g', 'c'):
        f = D + '%s_%x_%x.lean' % (kind.upper(), A, B)
        if os.path.exists(f): break
    else: raise Exception('no unit %x %x' % (A, B))
    t = open(f).read()
    pn = 'P' if kind == 'g' else 'PC'
    i = t.index('def %s_%x_%x ' % (pn, A, B)); j = t.index('\n\nset_option', i)
    d = t[i:j]
    m = re.match(r'def (\S+) \(s : State\) \(y3 : Nat\) (?:\(([^:]*) : Nat\) )?\(S\' : State\) : Prop :=\n  (.*)$', d, re.S)
    pname, invars, body = m.group(1), (m.group(2) or '').split(), m.group(3)
    ex = re.match(r'∃ ([^,]*), (.*)$', body, re.S)
    newvars = ex.group(1).split() if ex else []
    rest = ex.group(2) if ex else body
    lm = re.match(r'L%x s S\' ([^∧]*?)(?: ∧ |$)' % B, rest)
    outargs = lm.group(1).split()
    eqs = [] 
    if kind == 'g':
        import geq
        eqs = geq.eqs(A, B)
    else:
        eqs = [tuple(x) for x in eval(open(D + 'c_%x_%x.eqs' % (A, B)).read())]
    return dict(A=A, B=B, kind=kind, pname=pname, invars=invars, newvars=newvars, outargs=outargs, eqs=eqs, thm='%s_%x_%x' % (kind, A, B))
def emit(name, cuts):
    cuts = [int(c, 16) for c in cuts]
    units = [load(a, b) for a, b in zip(cuts, cuts[1:])]
    # rename each unit's input variables to the actual arguments (previous unit's outargs)
    for k in range(1, len(units)):
        u = units[k]; actual = units[k - 1]['outargs']
        mp = dict(zip(u['invars'], actual))
        sub = lambda s: re.sub(r'\bx[0-9a-f]+[a-z0-9]+\b', lambda m: mp.get(m.group(0), m.group(0)), s)
        u['eqs'] = [(n, sub(e)) for n, e in u['eqs']]
        u['outargs'] = [mp.get(a, a) for a in u['outargs']]
        u['invars_actual'] = actual
    A, Z = cuts[0], cuts[-1]
    imports = ''.join('import Fv256.Amd64.RecipG.%s_%x_%x\n' % (u['kind'].upper() if False else (u['kind'] if True else ''), u['A'], u['B']) for u in units)
    imports = ''.join('import Fv256.Amd64.RecipG.%s\n' % (('G_%x_%x' if u['kind'] == 'g' else 'C_%x_%x') % (u['A'], u['B'])) for u in units)
    invars = units[0]['invars']
    allnew = []; alleqs = []
    for u in units: allnew += u['newvars']; alleqs += u['eqs']
    outargs = units[-1]['outargs']
    L = 'PC_%x_%x' % (A, Z)
    eqtxt = ' ∧ '.join('%s = %s' % (n, e) for n, e in alleqs)
    pdef = ("def %s (s : State) (y3 : Nat) %s(S' : State) : Prop :=\n  ∃ %s, L%x s S' %s ∧ %s%sRecRegs s S' ∧ RecMem s S'.mem y3\n" %
            (L, ('(%s : Nat) ' % ' '.join(invars)) if invars else '', ' '.join(allnew), Z, ' '.join(outargs), eqtxt, ' ∧ ' if eqtxt else ''))
    st, _ = gseg.seg_stmt(A, Z, '%s s y3 %s' % (L, ' '.join(invars)))
    st = st.replace('theorem g_%x_%x' % (A, Z), 'theorem c_%x_%x' % (A, Z))
    out = imports + '\nopen Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic\n\nnamespace Fv256.Amd64.RecipSeg\n\n' + pdef + '\n'
    out += 'set_option maxHeartbeats 64000000 in\nset_option maxRecDepth 200000 in\n' + st
    # proof
    prev = dict(S='S', hpc='hpc', hR='hR', hM='hM', hL='hL', args=invars)
    lines = []
    for k, u in enumerate(units):
        call = '%s s %s hpc%d hs hR%d hM%d %s hL%d' % (u['thm'], prev['S'], k, k, k, ' '.join(prev['args']), k)
        call = '(%s (y3 := y3) s %s %s hs %s %s %s %s)' % (u['thm'], prev['S'], prev['hpc'], prev['hR'], prev['hM'], ' '.join(prev['args']), prev['hL'])
        if k < len(units) - 1:
            lines.append('  refine Fv256.SegCompose.seg_trans %s ?_' % call)
            lines.append('  intro S%d hpc%d hq%d' % (k + 1, k + 1, k + 1))
        else:
            lines.append('  refine Fv256.SegCompose.seg_mono %s ?_' % call)
            lines.append('  intro S%d hq%d' % (k + 1, k + 1))
        pn = u['pname']
        lines.append('  unfold %s at hq%d' % (pn, k + 1))
        names = u['newvars'] + ['hL%d' % (k + 1)] + ['h_' + n for n, e in u['eqs']] + ['hR%d' % (k + 1), 'hM%d' % (k + 1)]
        lines.append('  obtain ⟨%s⟩ := hq%d' % (', '.join(names), k + 1))
        prev = dict(S='S%d' % (k + 1), hpc='hpc%d' % (k + 1), hR='hR%d' % (k + 1), hM='hM%d' % (k + 1), hL='hL%d' % (k + 1), args=u['outargs'])
    lines.append('  unfold %s' % L)
    lines.append('  exact ⟨%s, hL%d, %s%shR%d, hM%d⟩' % (', '.join(allnew), len(units), ', '.join('h_' + n for n, e in alleqs), ', ' if alleqs else '', len(units), len(units)))
    # fix: intermediate hpc names: segments need S.rip = ..., provided by seg_trans callback (hpc_k)
    out += '\n'.join(lines) + '\n\nend Fv256.Amd64.RecipSeg\n'
    f = D + 'C_%x_%x.lean' % (A, Z)
    open(f, 'w').write(out)
    open(D + 'c_%x_%x.eqs' % (A, Z), 'w').write(repr(alleqs))
    open(D + 'c_%x_%x.obtain' % (A, Z), 'w').write('  unfold %s at h\n  obtain ⟨%s, hLz, %s%shRz, hMz⟩ := h\n' % (L, ', '.join(allnew), ', '.join('h_' + n for n, e in alleqs), ', ' if alleqs else ''))
    open(D + 'c_%x_%x.sig' % (A, Z), 'w').write('(s : State) (y3 : Nat) %s(S : State) (h : %s s y3 %s S)' % (('(%s : Nat) ' % ' '.join(invars)) if invars else '', L, ' '.join(invars)))
    return f
if __name__ == '__main__':
    f = emit(sys.argv[1], sys.argv[2:])
    print(f)
