#!/usr/bin/env python3
"""cs_inline_c2.py CORE_FILE CORE_THM THIN_FILE THIN_THM OPEN_NS : cs_live_a64.py's --inline with a thm_span that stops at docstrings and
finds THIN_THM after `namespace Witness`."""
import re, sys
src = open('scripts/cs_live_a64.py').read().split("if __name__ == '__main__':")[0]
exec(src)
def thm_span(s, name, nth=0, after=0):
    m = list(re.finditer(r'^theorem\s+' + re.escape(name) + r'\b', s[after:], re.M))[nth]
    m0 = after + m.start(); me = after + m.end()
    nxt = re.search(r'^(theorem|lemma|def|abbrev|end|namespace|/--|set_option|open|@\[)', s[me:], re.M)
    return m0, me + (nxt.start() if nxt else len(s) - me)
_orig = thm_span
a = sys.argv[1:]
_ts = thm_span
def thm_span2(s, name, nth=0):
    after = s.index('namespace Witness') if ('namespace Witness' in s and name in ('hex', 'nonvacuous', 'unquoted')) else 0
    return _ts(s, name, nth, after)
thm_span = thm_span2
inline_thin(a[0], a[1], a[2], a[3], a[4] if len(a) > 4 else None)
