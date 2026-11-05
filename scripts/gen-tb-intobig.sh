#!/bin/bash
# Generate (mechanically, not committed) the IntoBig proof modules re-targeted at ToBig's extraction:
# ToBig's extraction contains IntoBig as a second segment at ToBig+0x60, so every `Extracted.entry` of the IntoBig
# proofs becomes `(Extracted.entry + 0x60)`, and the modules live under Fv256/Arm64/TB/.
# usage: gen-tb-intobig.sh LEAN_DIR
L=${1:-lean}; D=$L/Fv256/Arm64; mkdir -p $D/TB
for m in IntoBigDefs IntoBigFinF IntoBigClose IntoBigLoop IntoBigTail IntoBigSlow3 IntoBigMid IntoBig; do
  dst=$m; [ "$m" = IntoBig ] && dst=IntoBigT   # the main module is IntoBig.lean; ToBig imports it as TB.IntoBigT
  python3 - "$D/$m.lean" "$D/TB/$dst.lean" <<'PY'
import re,sys
s=open(sys.argv[1]).read()
if 'namespace Witness' in s:
    i=s.index('namespace Witness'); j=s.index('end Witness')+len('end Witness')
    s=s[:i]+s[j:]
s=s.replace('Extracted.entry','(Extracted.entry + 0x60)')
s=s.replace('Extracted.program.link impl','(Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).IntoBig"]).link impl')
s=re.sub(r'import Fv256\.Arm64\.(IntoBig\w+)',r'import Fv256.Arm64.TB.\1',s)
open(sys.argv[2],'w').write(s)
PY
done
