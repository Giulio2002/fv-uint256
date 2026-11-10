#!/bin/bash
# amd64 twin of gen-tb-intobig.sh (FV-C): the IntoBig proof modules re-targeted at ToBig's extraction, where IntoBig is
# the second segment at ToBig+0x60. Output: Fv256/Amd64/TB/<module>.lean (generated, not committed); the main module
# Amd64/IntoBigT.lean becomes TB/IntoBigT.lean.
# usage: gen-tb-intobig-amd64.sh LEAN_DIR
L=${1:-lean}; D=$L/Fv256/Amd64; mkdir -p $D/TB
for m in IntoBigDefs IntoBigFinF IntoBigClose IntoBigLoop IntoBigTail IntoBigSlow3 IntoBigMid IntoBigT; do
  src=$m; [ "$m" = IntoBigT ] && src=IntoBig   # the amd64 main module is IntoBig.lean (IntoBigT.lean no longer exists); its TB copy is TB/IntoBigT.lean
  python3 - "$D/$src.lean" "$D/TB/$m.lean" <<'PY'
import re,sys
s=open(sys.argv[1]).read()
if 'namespace Wit' in s:
    i=s.index('namespace Wit'); j=s.index('end Wit')+len('end Wit')
    s=s[:i]+s[j:]
# the claim layout renamed the proof theorem `correctness` -> `correctness_proof`; the re-targeted copies keep the name their users
# (ToBig, Format) call, so the generated modules are unchanged
assert s.count('theorem correctness_proof')<=1
s=s.replace('theorem correctness_proof','theorem correctness')
s=s.replace('Extracted.entry','(Extracted.entry + 0x60)')
s=s.replace('Extracted.program.link impl','(Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).IntoBig"]).link impl')
s=re.sub(r'import Fv256\.Amd64\.(IntoBig\w+)',r'import Fv256.Amd64.TB.\1',s)
open(sys.argv[2],'w').write(s)
PY
done
