#!/bin/bash
cd /srv/fv-uint256-wJ
D=/srv/fv-uint256-wJ/lean/Fv256/Amd64
for f in UnmarshalSpec UnmarshalDec UnmarshalHex UnmarshalDecJ UnmarshalQ UnmarshalJSON0 UnmarshalJa UnmarshalJc UnmarshalJd UnmarshalJq UnmarshalJSON UnmarshalJSONAudit; do
  s=$(date +%s)
  HEAVY_PRIORITY=0 /srv/janus-ops/bin/heavy-run -- build/lcn.sh auj $D/$f.lean > logs/c4_$f.log 2>&1
  echo "DONE $f t=$(( $(date +%s)-s )) $(grep LEANRC logs/c4_$f.log)" >> logs/c_chain4.out
  grep -q "LEANRC=0" logs/c4_$f.log || break
done
echo ENDMARK >> logs/c_chain4.out
