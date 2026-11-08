#!/usr/bin/env python3
"""scripts/callsite-splice.py FILE THEOREM [--block BLOCKFILE] [--conj TEXT --proof TERM]...  (idempotent)

Adds U-WITNESS-CALLSITE conjuncts to ONE witness theorem of FILE:
  * --block F : text of F (defs + pre lemmas of the call-site states) is inserted just before the declaration of the
                witness theorem (first line starting with `theorem THEOREM`, plus any docstring right above it) once
                (marker `-- CALLSITE-BLOCK <name>` makes it idempotent; pass --block-name NAME, default = basename of F)
  * each --conj/--proof pair: the conjunct text is inserted in the statement right before the `Returns (` conjunct, the proof
    term right before the last `correctness ` token of the proof.
THEOREM is the declared (unqualified) name, e.g. `nonvacuous`, `big`, `nil`, `hex`, `unquoted`.
Repeat the file for each theorem of a multi-witness file; for a same-name theorem in different namespaces pass --nth K (0-based)."""
import sys, re, argparse

ap = argparse.ArgumentParser()
ap.add_argument('file'); ap.add_argument('theorem')
ap.add_argument('--block'); ap.add_argument('--block-name')
ap.add_argument('--conj', action='append', default=[]); ap.add_argument('--proof', action='append', default=[])
ap.add_argument('--nth', type=int, default=0)
a = ap.parse_args()
assert len(a.conj) == len(a.proof)
src = open(a.file).read()
ms = [m for m in re.finditer(r'^theorem\s+' + re.escape(a.theorem) + r'\b', src, re.M)]
m = ms[a.nth]
start = m.start()
# extent: up to the next top-level declaration / end line
nxt = re.search(r'^(theorem|lemma|example|def|abbrev|end|namespace|/--|set_option|open|@\[)\b', src[m.end():], re.M)
end = m.end() + (nxt.start() if nxt else len(src) - m.end())
body = src[start:end]
if a.conj:
    if a.conj[0] in body:
        print('already spliced', a.theorem); sys.exit(0)
    i = body.find('Returns (')
    assert i >= 0, 'no Returns( in statement'
    ins = ''.join('(' + c + ') ∧\n    ' for c in a.conj)
    body = body[:i] + ins + body[i:]
    j = body.rfind('correctness ')
    assert j >= 0, 'no correctness in proof'
    insp = ''.join(p + ',\n    ' for p in a.proof)
    body = body[:j] + insp + body[j:]
    body = body.rstrip('\n') + '\n'
src = src[:start] + body + src[end:]
if a.block:
    name = a.block_name or a.file
    mk = '-- CALLSITE-BLOCK ' + (a.block_name or a.block)
    if mk not in src:
        blk = open(a.block).read().rstrip('\n') + '\n\n'
        # insert before the docstring directly above the theorem (if any)
        m2 = [mm for mm in re.finditer(r'^theorem\s+' + re.escape(a.theorem) + r'\b', src, re.M)][a.nth]
        pos = m2.start()
        pre = src[:pos]
        dm = re.search(r'/--(?:(?!-/).)*-/\n$', pre, re.S)
        if dm: pos = dm.start()
        src = src[:pos] + mk + '\n' + blk + src[pos:]
open(a.file, 'w').write(src)
print('spliced', a.theorem, 'conj', len(a.conj))
