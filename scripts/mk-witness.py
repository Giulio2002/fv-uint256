#!/usr/bin/env python3
"""Replace the anonymous `example := correctness ...` of a Witness by a named `nonvacuous : ∃ ...` theorem with one
conjunct per hypothesis of `correctness` (contract hypotheses included), the call-state facts and the precondition."""
import re, sys

def groups(s, i, o='(', c=')'):
    """balanced group starting at s[i]==o; returns end index (exclusive)"""
    d = 0
    for j in range(i, len(s)):
        if s[j] == o: d += 1
        elif s[j] == c:
            d -= 1
            if d == 0: return j + 1
    raise ValueError

def split_args(t):
    out, i = [], 0
    while i < len(t):
        if t[i].isspace(): i += 1; continue
        if t[i] == '(':
            j = groups(t, i); out.append(t[i:j]); i = j
        else:
            j = i
            while j < len(t) and not t[j].isspace(): j += 1
            out.append(t[i:j]); i = j
    return out

path = sys.argv[1]
src = open(path).read()
a = src.index('theorem correctness')
b = src.index(':= by', a)
hdr = src[a:b]
# binders: from after name to the ':' that precedes Ensures
m = re.search(r'\n\s*:\s*\n?\s*(EnsuresGo|Ensures)\b|\)\s*:\s*\n\s*(EnsuresGo|Ensures)\b', hdr)
k = re.search(r'(EnsuresGo|Ensures)\s', hdr).start()
bind_txt = hdr[len('theorem correctness'):k]
bind_txt = bind_txt[:bind_txt.rindex(':')]
bs, i = [], 0
while i < len(bind_txt):
    if bind_txt[i] == '(':
        j = groups(bind_txt, i); bs.append(bind_txt[i + 1:j - 1]); i = j
    else: i += 1
vals, hyps = [], []   # (names, type)
for g in bs:
    names, ty = g.split(' : ', 1)
    names = names.split()
    (hyps if names[0] in ('hnew','hmk','hwb1','hwb2') else vals).append((names, ty.strip()))
rest = hdr[k:]
mm = re.match(r'(EnsuresGo|Ensures)\s+(\(.*?\))\s+Extracted\.entry\s+(\[[^\]]*\])\s*\n', rest, re.S)
prog, args = mm.group(2), mm.group(3)
pstart = mm.end()
while rest[pstart].isspace(): pstart += 1
pend = groups(rest, pstart)
pre = rest[pstart:pend].strip()
assert pre.startswith('(fun s =>'), pre[:30]
pre_body = pre[len('(fun s =>'):-1].strip()
# the example
em = re.search(r'(/--[^\n]*-/\n)?example := correctness ([^\n]*)\n', src)
ex_args = split_args(em.group(2))
binder_names = [n for (ns, _) in vals + hyps for n in ns]
allb = []
for g in bs:
    names, _ = g.split(' : ', 1)
    allb += names.split()
nb = len(allb)
bind_vals = dict(zip(allb, ex_args[:nb]))
ret_, hret_, s0_, setup_, pre_ = ex_args[nb:nb + 5]
val_names = [n for (ns, _) in vals for n in ns]
hyp_names = [n for (ns, _) in hyps for n in ns]
argnames = set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*', args))
KEEP = {'impl', 'rt', 'H', 'R', 'b'} | argnames
kept, free = [], []
for ns, ty in vals:
    k = [n for n in ns if n in KEEP]
    if k: kept.append((k, ty))
    for n in ns:
        if n not in KEEP: free.append((n, ty))
# free variables: they stay existential, pinned to their type by a conjunct of a typed local def
pins, pin_defs = [], {}
for n, ty in free:
    d = 'pin' + re.sub(r'[^A-Za-z0-9]', '', ty)
    pin_defs[d] = ty
    pins.append('%s %s' % (d, n))
kept = kept + [([n], ty) for n, ty in free]
pre_body = ' ∧\n    '.join(pins + [pre_body]) if pins else pre_body
ex_binders = ' '.join('(%s : %s)' % (' '.join(ns), ty) for ns, ty in kept)
hyp_txt = ' ∧\n    '.join(ty for _, ty in hyps)
if hyp_txt: hyp_txt += ' ∧\n    '
kept_names = [n for ns, _ in kept for n in ns]
tup = [bind_vals[n] for n in kept_names] + [ret_, s0_] + [bind_vals[n] for n in hyp_names] + [hret_, setup_]
tup.append('⟨%s⟩' % ', '.join(['trivial'] * len(pins) + [pre_]) if pins else pre_)
pindefs = ''.join('/-- pins the type of an existential variable of `nonvacuous` -/\ndef %s (_k : %s) : Prop := True\n\n' % (d, t) for d, t in pin_defs.items())
thm = pindefs + ('/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `rt`, `H`), the contract hypotheses, an admissible\n'
       'return address, a call state and the precondition. -/\n'
       'theorem nonvacuous : ∃ %s (ret : Nat) (s : State),\n    %sRetAddr (Extracted.program.link impl) ret ∧\n'
       '    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry %s s ∧\n    (%s) :=\n  ⟨%s⟩\n'
       % (ex_binders, hyp_txt, args, pre_body, ', '.join(tup)))
src = src[:em.start()] + thm + src[em.end():]
open(path, 'w').write(src)
print('ok', path)
