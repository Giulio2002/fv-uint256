#!/bin/bash
# lihm.sh : like lih.sh but hexstep/hexbase proofs replaced by sorry (fast main iteration)
export PATH=$PATH:/usr/local/go/bin
WS=/srv/janus-ops/jcache-shared/v1/consumer/22911f2cdbd3defee197aa02/fec189886b833a69832bf1b2
python3 - <<'PY'
import re
src=open('/srv/fv-uint256-wh/lean/Fv256/Amd64/Hex.lean').read()
for name in ['hexstep','hexbase']:
    i=src.index('theorem '+name)
    j=src.index(':= by\n',i)+len(':= by\n')
    # end: next top-level decl
    m=re.search(r'\n(set_option|theorem|namespace|end |/--)',src[j:])
    k=j+m.start()+1
    src=src[:j]+'  sorry\n\n'+src[k:]
open('/srv/janus-ops/jcache-shared/v1/consumer/22911f2cdbd3defee197aa02/fec189886b833a69832bf1b2/root/Fv256/Amd64/Hex.lean','w').write(src)
PY
cd $WS/root
memcap -m 16G lake env lean Fv256/Amd64/Hex.lean 2>&1 | grep -v "deprecated\|unused\|Hint\|Note\|^$" | cut -c1-400
echo ENDMARK
