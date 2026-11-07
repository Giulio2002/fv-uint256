#!/bin/bash
cd /srv/fv-uint256-wJ
for f in UnmarshalJa UnmarshalJc UnmarshalJd UnmarshalJq UnmarshalJSON UnmarshalJSONAudit; do
  s=$(date +%s)
  HEAVY_PRIORITY=0 /srv/janus-ops/bin/heavy-run -- /usr/bin/time -v build/lcn.sh auj /srv/fv-uint256-wJ/lean/Fv256/Amd64/$f.lean > logs/c6_$f.log 2>&1
  echo "DONE $f t=$(( $(date +%s)-s )) $(grep LEANRC logs/c6_$f.log) rss_kb=$(grep 'Maximum res' logs/c6_$f.log | awk '{print $NF}')" >> logs/c_chain6.out
  grep -q "LEANRC=0" logs/c6_$f.log || break
done
echo ENDMARK >> logs/c_chain6.out
