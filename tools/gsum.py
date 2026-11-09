#!/usr/bin/env python3
"""gsum.py NAME A Z 'bounds' 'facts' 'tail' -> prints a summary-lemma skeleton for chain c_A_Z.
Statement: sig of the chain, (bounds) , conclusion ∃ <new outargs of L_Z>, L_Z s S <outargs> ∧ facts. Proof: obtain; have key : facts := by subst <all eqs>; <tail>; exact ⟨_,..,hLz,key⟩"""
import re, sys, ast
D = '/srv/fv-uint256-wBm/lean/Fv256/Proofs/Amd64/RecipG/'
def make(name, A, Z, bounds, facts, tail, pre='', unfold=''):
    sig = open(D + 'c_%s_%s.sig' % (A, Z)).read().strip()
    ob = open(D + 'c_%s_%s.obtain' % (A, Z)).read().split('\n')[1].strip()
    names = re.findall(r'h_x[0-9a-z]+', ob)
    t = open(D + 'C_%s_%s.lean' % (A, Z)).read()
    outargs = re.search(r"L%s s S' ([^∧]*)" % Z, t).group(1).split()
    invars = re.search(r'\(s : State\) \(y3 : Nat\) \(([^:]*) : Nat\)', sig).group(1).split()
    new = [a for a in outargs if a not in invars]
    ex = ('∃ %s, ' % ' '.join(new)) if new else ''
    thm = 'theorem %s %s\n    %s:\n    %sL%s s S %s ∧\n      %s := by\n  %s\n  have key : %s := by\n    %ssubst %s\n    %s%s\n  exact ⟨%shLz, key⟩\n' % (
        name, sig, bounds + ' ' if bounds else '', ex, Z, ' '.join(outargs), facts, ob, facts, (pre + '\n    ') if pre else '', ' '.join(names), (unfold + '\n    ') if unfold else '', tail,
        ('_, ' * len(new)))
    return thm
if __name__ == '__main__':
    n, A, Z, b, f, tl = sys.argv[1:7]
    print(make(n, A, Z, b, f, tl))
