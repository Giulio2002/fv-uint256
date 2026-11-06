#!/usr/bin/env python3
"""g4anf.py: A-normal-form proof helper: given the equations of a unit, produce Lean tactic lines that replace every `A / 2^64`, `A % 2^64`
subterm by fresh variables (with the facts  2^64 * c + m = A,  m < 2^64)  so that a final `omega` only sees linear equalities."""
import re
D64 = '18446744073709551616'
def tokenize(s):
    return re.findall(r'\(|\)|\+|\*|/|%|[A-Za-z0-9_]+', s)
class P:
    def __init__(self, toks): self.t = toks; self.i = 0
    def peek(self): return self.t[self.i] if self.i < len(self.t) else None
    def next(self): x = self.t[self.i]; self.i += 1; return x
    def expr(self):
        a = self.mul()
        while self.peek() == '+':
            self.next(); b = self.mul(); a = ('+', a, b)
        return a
    def mul(self):
        a = self.atom()
        while self.peek() in ('*', '/', '%'):
            op = self.next(); b = self.atom(); a = (op, a, b)
        return a
    def atom(self):
        x = self.next()
        if x == '(':
            e = self.expr(); assert self.next() == ')'; return e
        return x
def parse(s):
    p = P(tokenize(s)); e = p.expr(); assert p.peek() is None, (s, p.i); return e
def show(e, sub):
    if isinstance(e, str): return e
    k = id(e)
    op, a, b = e
    key = (op, show_raw(e))
    if key in sub: return sub[key]
    return '(%s %s %s)' % (show(a, sub), op, show(b, sub))
def show_raw(e):
    if isinstance(e, str): return e
    return '(%s %s %s)' % (show_raw(e[1]), e[0], show_raw(e[2]))
def anf(eqs_exprs, tag='t'):
    """eqs_exprs: list of Lean expression strings. Returns (lines, mapping raw->name, new expr strings)."""
    sub = {}; lines = []; cnt = [0]
    def visit(e):
        if isinstance(e, str): return
        op, a, b = e
        visit(a); visit(b)
        if op in ('/', '%') and b == D64:
            key = (op, show_raw(e))
            if key in sub: return
            # ensure the partner is declared together
            A = a
            Atxt = show(A, sub)
            c = '%sc%d' % (tag, cnt[0]); m = '%sm%d' % (tag, cnt[0]); cnt[0] += 1
            keyd = ('/', show_raw(('/', A, D64))); keym = ('%', show_raw(('%', A, D64)))
            lines.append('  have %sd := Nat.div_add_mod (%s) %s' % (c, Atxt, D64))
            lines.append('  have %sl := Nat.mod_lt (%s) (show %s > 0 by decide)' % (m, Atxt, D64))
            lines.append('  generalize (%s) / %s = %s at *' % (Atxt, D64, c))
            lines.append('  generalize (%s) %% %s = %s at *' % (Atxt, D64, m))
            sub[keyd] = c; sub[keym] = m
    for s in eqs_exprs: visit(parse(s))
    return lines
