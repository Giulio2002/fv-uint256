#!/usr/bin/env python3
"""a64chain.py NAME c0 c1 ... ck : compose consecutive generated arm64 segments/chains (cut ABSOLUTE addresses hex) into one chain unit
lean/Fv256/Proofs/Arm64/RecipG/C_A_Z.lean (theorem c_A_Z, def PC_A_Z) + sidecar .json. Units: G_A_B.lean (g) or C_A_B.lean (c)."""
import re, sys, os, json
sys.path.insert(0, os.path.dirname(__file__))
import a64gen as G
ROOT = G.ROOT
D = ROOT + '/lean/Fv256/Proofs/Arm64/RecipG/'
def split_top(s, sep=' ∧ '):
    out = []; d = 0; cur = ''; i = 0
    while i < len(s):
        ch = s[i]
        if ch in '(⟨': d += 1
        elif ch in ')⟩': d -= 1
        if d == 0 and s.startswith(sep, i):
            out.append(cur); cur = ''; i += len(sep); continue
        cur += ch; i += 1
    out.append(cur); return out
def load(a, b):
    """a, b: entry offsets (ints)"""
    if os.path.exists(D + 'C_%x_%x.json' % (a, b)):
        d = json.load(open(D + 'C_%x_%x.json' % (a, b))); return d
    f = D + 'G_%x_%x.lean' % (a, b)
    t = open(f).read()
    i = t.index('def P_%x_%x ' % (a, b)); j = t.index('\n\nset_option', i)
    dd = t[i:j]
    m = re.match(r"def (\S+) \(s : State\) (?:\(([^:]*) : Nat\) )?\(S' : State\) : Prop :=\n  (.*)$", dd, re.S)
    invars = (m.group(2) or '').split(); body = m.group(3)
    ex = re.match(r'∃ ([^,]*), (.*)$', body, re.S)
    newvars = ex.group(1).split() if ex else []
    rest = ex.group(2) if ex else body
    parts = split_top(rest)
    lm = re.match(r"L%x S' (.*)$" % b, parts[0], re.S)
    outargs = lm.group(1).split()
    facts = parts[1:-2]   # drop RecRegs, RecMem
    assert parts[-2].startswith('RecRegs') and parts[-1].startswith('RecMem'), parts[-2:]
    # classify: equations 'name = ...' with name a new var vs. extras
    eqs = []; extras = []
    for ft in facts:
        mm = re.match(r'(x[0-9a-f]+[rm][0-9]+) = ', ft)
        if mm and mm.group(1) in newvars: eqs.append((mm.group(1), ft[len(mm.group(0)):]))
        else: extras.append(ft)
    nextra_in = len(G.EXTRA.get(a, []))
    return dict(A=a, B=b, kind='g', invars=invars, newvars=newvars, outargs=outargs, eqs=eqs, extras=extras, nextra_in=nextra_in)
def ren(mp, s): return re.sub(r'\bx[0-9a-f]+[rm][0-9]+\b', lambda m: mp.get(m.group(0), m.group(0)), s)
def emit(name, cuts):
    offs = [G.off(int(c, 16)) for c in cuts]
    units = [load(a, b) for a, b in zip(offs, offs[1:])]
    for k in range(1, len(units)):
        u = units[k]; actual = units[k - 1]['outargs']
        mp = dict(zip(u['invars'], actual))
        u['eqs'] = [(n, ren(mp, e)) for n, e in u['eqs']]
        u['extras'] = [ren(mp, e) for e in u['extras']]
        u['outargs'] = [mp.get(a, a) for a in u['outargs']]
        u['invars'] = actual
    A, Z = offs[0], offs[-1]
    imports = ''.join('import Fv256.Proofs.Arm64.RecipG.%s_%x_%x\n' % (u.get('kind', 'g').upper(), u['A'], u['B']) for u in units)
    invars = units[0]['invars']
    allnew = []; alleqs = []; allextras = []
    for u in units: allnew += u['newvars']; alleqs += u['eqs']; allextras += u['extras']
    outargs = units[-1]['outargs']
    L = 'PC_%x_%x' % (A, Z)
    facts = ['%s = %s' % (n, e) for n, e in alleqs] + allextras
    pre_extra = G.EXTRA.get(A, [])
    pdef = ("def %s (s : State) %s(S' : State) : Prop :=\n  ∃ %s, L%x S' %s ∧ %s%sRecRegs s S' ∧ RecMem s S'.mem\n" %
            (L, ('(%s : Nat) ' % ' '.join(invars)) if invars else '', ' '.join(allnew) if allnew else '_u', Z, ' '.join(outargs), ' ∧ '.join(facts), ' ∧ ' if facts else ''))
    if not allnew: pdef = pdef.replace('∃ _u, ', '')
    st, _ = G.seg_stmt(int(cuts[0], 16), int(cuts[-1], 16), '%s s %s' % (L, ' '.join(invars)))
    st = st.replace('theorem g_%x_%x' % (A, Z), 'theorem c_%x_%x' % (A, Z))
    out = HDR_IMPORTS(units) + '\nopen Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec\n\nnamespace Fv256.Arm64.RecipSeg\nset_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\n\n' + pdef + '\n'
    out += 'set_option maxHeartbeats 64000000 in\nset_option maxRecDepth 200000 in\n' + st
    prev = dict(S='S', hpc='hpc', hR='hR', hM='hM', hL='hL', args=invars, hx=['hX%d' % j for j in range(len(pre_extra))])
    lines = []
    for k, u in enumerate(units):
        call = '(g_%x_%x s %s %s hs %s %s %s %s%s)' % (u['A'], u['B'], prev['S'], prev['hpc'], prev['hR'], prev['hM'], ' '.join(prev['args']), prev['hL'], ''.join(' ' + h for h in prev['hx']))
        if k < len(units) - 1:
            lines.append('  refine Fv256.Arm64.SegCompose.seg_trans %s ?_' % call)
            lines.append('  intro S%d hpc%d hq%d' % (k + 1, k + 1, k + 1))
        else:
            lines.append('  refine Fv256.Arm64.SegCompose.seg_mono %s ?_' % call)
            lines.append('  intro S%d hq%d' % (k + 1, k + 1))
        lines.append('  unfold P_%x_%x at hq%d' % (u['A'], u['B'], k + 1))
        hxn = ['hx%d_%d' % (k + 1, j) for j in range(len(u['extras']))]
        names = u['newvars'] + ['hL%d' % (k + 1)] + ['h_' + n for n, e in u['eqs']] + hxn + ['hR%d' % (k + 1), 'hM%d' % (k + 1)]
        lines.append('  obtain ⟨%s⟩ := hq%d' % (', '.join(names), k + 1))
        prev = dict(S='S%d' % (k + 1), hpc='hpc%d' % (k + 1), hR='hR%d' % (k + 1), hM='hM%d' % (k + 1), hL='hL%d' % (k + 1), args=u['outargs'], hx=hxn)
        u['hxn'] = hxn
    lines.append('  unfold %s' % L)
    allhx = [h for u in units for h in u['hxn']]
    lines.append('  exact ⟨%s, hL%d, %s%shR%d, hM%d⟩' % (', '.join(allnew), len(units), ', '.join(['h_' + n for n, e in alleqs] + allhx), ', ' if (alleqs or allhx) else '', len(units), len(units)))
    out += '\n'.join(lines) + '\n\nend Fv256.Arm64.RecipSeg\n'
    f = D + 'C_%x_%x.lean' % (A, Z)
    open(f, 'w').write(out)
    meta = dict(A=A, B=Z, kind='c', invars=invars, newvars=allnew, outargs=outargs, eqs=alleqs, extras=allextras, nextra_in=len(pre_extra))
    json.dump(meta, open(D + 'C_%x_%x.json' % (A, Z), 'w'))
    open(D + 'c_%x_%x.obtain' % (A, Z), 'w').write('  unfold %s at h\n  obtain ⟨%s, hLz, %s%shRz, hMz⟩ := h\n' % (L, ', '.join(allnew), ', '.join(['h_' + n for n, e in alleqs] + allhx), ', ' if (alleqs or allhx) else ''))
    return f
def HDR_IMPORTS(units):
    return ''.join('import Fv256.Proofs.Arm64.RecipG.%s_%x_%x\n' % ('C' if u.get('kind') == 'c' else 'G', u['A'], u['B']) for u in units)
if __name__ == '__main__':
    print(emit(sys.argv[1], sys.argv[2:]))
