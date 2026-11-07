#!/bin/bash
# The ToBig IntoBig proof modules (Fv256/Amd64/TB/*, IntoBig as the second segment at ToBig+0x60) re-targeted at Format's extraction,
# where IntoBig is the segment at 0x4b1760 (build/ex2-amd64-Format of /srv/fv-uint256-wf2). Output: Fv256/Amd64/FM/<module>.lean
# (generated, not committed). The addresses inside IntoBig are all derived from its entry (`ripTarget`), so the entry literal is
# the only change; the module namespace is kept (a file imports either the TB or the FM chain, never both).
# usage: gen-fm-intobig-amd64.sh LEAN_DIR
L=${1:-lean}; D=$L/Fv256/Amd64; mkdir -p $D/FM
for m in IntoBigDefs IntoBigFinF IntoBigClose IntoBigLoop IntoBigTail IntoBigSlow3 IntoBigMid IntoBigT; do
  python3 - "$D/TB/$m.lean" "$D/FM/$m.lean" <<'PY'
import re,sys
s=open(sys.argv[1]).read()
n=s.count('(Extracted.entry + 0x60)')
s=s.replace('(Extracted.entry + 0x60)','0x4b1760')
assert 'Extracted.entry' not in s, 'an Extracted.entry that is not ToBig+0x60 is left'
s=re.sub(r'import Fv256\.Amd64\.TB\.(IntoBig\w+)',r'import Fv256.Amd64.FM.\1',s)
open(sys.argv[2],'w').write(s)
PY
done
