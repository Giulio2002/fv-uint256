#!/usr/bin/env python3
"""cs-scan-apply.py : wire the Scan witnesses (amd64): block into ScanWitC (before contracts_ok), statement conjuncts + proof terms in the 5 witnesses of Scan.lean."""
import re, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cs_live_gen import block
cfg = dict(s0='s0', B='0x400', R2='(R3 TW)', nok=6, pos=dict(new=0, w1=1, w2=2, mg=3, mv=4, sb=5), new_or=True, newty='numErrT',
           dst='zW', src='0x301000', sb=True, sb_addr='sbAddr', st_addr='stAddr', sb_buf='0', sb_p='0x301000',
           sb_ok='⟨rfl, 0, 0x301000, by decide⟩', mv_ok='⟨rfl, zW, 0x301000, 1, by decide, by decide, by decide⟩', inv0='(inv0 twS dwS)')
D = '/srv/fv-uint256-csb/lean/Fv256/Amd64/'
defs, stmt, terms = block(cfg)
f = D + 'ScanWitC.lean'; s = open(f).read()
if 'csNew_pre' not in s:
    i = s.index('/-- the contracts of `Scan.correctness` hold of the stub runtime -/')
    s = s[:i] + 'open Fv256.CallSites\n\ndef s0 : State := st twS dwS\n\n' + defs + '\n' + s[i:]
    s = s.replace('import Extracted\n', 'import Extracted\nimport Fv256.Amd64.CallSites.Live\n', 1)
    open(f, 'w').write(s)
f = D + 'Scan.lean'; s = open(f).read()
if 'csNew_pre' not in s:
    s = s.replace('import Extracted\n', 'import Extracted\nimport Fv256.Amd64.CallSites.Live\n', 1)
    # statements: before each `RetAddr (Extracted.program.link impl) ret ∧` after a `theorem nonvacuous`
    parts = s.split('theorem nonvacuous')
    out = [parts[0]]
    q = 'Fv256.Amd64.Scan.Witness.'
    tq = ', '.join(re.sub(r'\b(cs(?:New|Mg|Mv|W1|W2|Cm|If|Sb)(?:_rip|_pre)?)\b', q + r'\1', x) for x in terms)
    for p in parts[1:]:
        r = p.index('    RetAddr (Extracted.program.link impl) ret ∧')
        p = p[:r] + stmt + p[r:]
        m = re.search(r'(\S*Witness\.hret) ', p)
        p = p[:m.start()] + tq + ', ' + p[m.start():]
        out.append(p)
    s = 'theorem nonvacuous'.join(out)
    open(f, 'w').write(s)
