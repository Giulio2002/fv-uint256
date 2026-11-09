#!/usr/bin/env python3
"""Tiny top-level command splitter for the (machine-formatted, column-0) Lean files of this repository.

split(text) -> list of Cmd(start, end, kind, head, first_line, last_line): contiguous, covering the whole text after the import block.
Comments (`--`, nested `/- -/`) and string literals are skipped, so column-0 prose inside `/-! ... -/` is never mistaken for a command.
A doc comment (`/-- ... -/`) belongs to the command that follows it; `open X in` / `set_option .. in` / `attribute [..] in` glue to the next command.
The result is validated against Lean's own declaration ranges by restructure.py (every moved declaration must start at a command boundary).
"""
import re
from dataclasses import dataclass

KW = ('import', 'open', 'set_option', 'namespace', 'end', 'section', 'variable', 'universe', 'theorem', 'lemma', 'def', 'abbrev',
      'instance', 'structure', 'inductive', 'class', 'example', 'macro', 'elab', 'syntax', 'notation', 'infix', 'infixl', 'infixr',
      'prefix', 'postfix', 'attribute', 'deriving', 'opaque', 'axiom', 'macro_rules', 'declare_syntax_cat', 'initialize', 'mutual',
      'elab_rules', 'register_simp_attr', 'run_cmd', 'local', 'scoped', 'private', 'protected', 'noncomputable', 'partial', 'unsafe',
      'nonrec', 'add_decl_doc', 'export', 'builtin_initialize', 'compile_inductive', 'alias')
KWRE = re.compile(r'(?:@\[|#[a-z_]+|(?:' + '|'.join(KW) + r')(?![A-Za-z0-9_\'!?.]))')
MODS = {'private', 'protected', 'noncomputable', 'partial', 'unsafe', 'nonrec', 'local', 'scoped'}


@dataclass
class Cmd:
    start: int
    end: int
    kind: str       # first non-modifier keyword (or 'comment' / 'attr' / 'hash')
    head: str       # first line of the command, stripped
    line0: int      # 1-based first line (incl. doc comment)
    line1: int      # 1-based last line


def _scan(text):
    """yield (pos, kind) for column-0 tokens outside comments: kind in {'doc', 'mod', 'cmt', 'cmd'}"""
    i, n = 0, len(text)
    depth = 0
    out = []
    bol = True
    while i < n:
        c = text[i]
        if depth > 0:
            if text.startswith('/-', i): depth += 1; i += 2; continue
            if text.startswith('-/', i): depth -= 1; i += 2; continue
            i += 1; continue
        if c == '\n': bol = True; i += 1; continue
        if text.startswith('--', i):
            j = text.find('\n', i); i = n if j < 0 else j; continue
        if text.startswith('/-', i):
            kind = 'doc' if text.startswith('/--', i) else ('cmt' if text.startswith('/-!', i) else 'bc')
            if bol and (i == 0 or text[i - 1] == '\n'): out.append((i, kind))
            depth = 1; i += 2; bol = False; continue
        if c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            i += 1; bol = False; continue
        if c == "'" and i + 2 < n and (text[i + 2] == "'" or (text[i + 1] == '\\')):
            i += 3; bol = False; continue
        if bol and (i == 0 or text[i - 1] == '\n') and not c.isspace():
            m = KWRE.match(text, i)
            if m: out.append((i, 'cmd'))
        if not c.isspace(): bol = False
        i += 1
    return out


def split(text):
    toks = _scan(text)
    starts = []   # (pos, kind)
    pend = None
    for pos, k in toks:
        if k == 'doc':
            if pend is None: pend = pos
            continue
        if k == 'bc':
            continue
        if k == 'cmt':
            starts.append((pos, 'comment')); pend = None; continue
        p = pend if pend is not None else pos
        pend = None
        starts.append((p, 'cmd'))
    cmds = []
    for idx, (p, k) in enumerate(starts):
        e = starts[idx + 1][0] if idx + 1 < len(starts) else len(text)
        body = text[p:e]
        cmds.append([p, e, k, body])
    # glue `... in` prefixes to the following command
    res = []
    glue = None
    for p, e, k, body in cmds:
        if glue is not None:
            p = glue; glue = None
        if k == 'cmd':
            first = ''
            # last code token of the command's first logical line: strip comments crudely
            code = re.sub(r'--[^\n]*', '', body).rstrip()
            if re.match(r'^(open|set_option|attribute|universe)\b', code.lstrip('@[ ')) and re.search(r'\bin\s*$', code) and '\n\n' not in code.strip():
                glue = p; continue
        res.append((p, e, k, text[p:e]))
    out = []
    for p, e, k, body in res:
        stripped = body.lstrip()
        kind = k
        if k == 'cmd':
            t = stripped
            while True:       # glued `open X in` / `set_option o v in` / `attribute [..] in` prefixes
                m = re.match(r'(?:open|set_option|attribute|universe)\b[^\n]*\bin[ \t]*(?:--[^\n]*)?\n\s*', t)
                if not m: break
                t = t[m.end():]
            if t.startswith('/--'):
                j = t.find('-/'); d = 1; q = 3
                while q < len(t) and d:
                    if t.startswith('/-', q): d += 1; q += 2
                    elif t.startswith('-/', q): d -= 1; q += 2
                    else: q += 1
                t = t[q:].lstrip()
            while True:
                if t.startswith('@['):
                    d = 0
                    for q, ch in enumerate(t):
                        if ch == '[': d += 1
                        elif ch == ']':
                            d -= 1
                            if d == 0: break
                    t = t[q + 1:].lstrip(); continue
                m = re.match(r'(\w+)\s', t)
                if m and m.group(1) in MODS: t = t[m.end():].lstrip(); continue
                break
            m = re.match(r"[#\w']+", t)
            kind = m.group(0) if m else '?'
            if kind == 'in': kind = '?'
        head = body.strip().split('\n', 1)[0].strip()
        l0 = text.count('\n', 0, p) + 1
        l1 = text.count('\n', 0, p + len(body.rstrip())) + 1
        out.append(Cmd(p, e, kind, head, l0, l1))
    return out


DECL_KINDS = {'theorem', 'lemma', 'def', 'abbrev', 'instance', 'structure', 'inductive', 'class', 'opaque', 'axiom', 'example'}
CTX_KINDS = {'open', 'set_option', 'namespace', 'end', 'section', 'variable', 'universe', 'export'}

if __name__ == '__main__':
    import sys
    t = open(sys.argv[1]).read()
    for c in split(t):
        print(c.line0, c.line1, c.kind, c.head[:90])
