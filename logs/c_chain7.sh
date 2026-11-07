#!/bin/bash
cd /srv/fv-uint256-wJ
D=/srv/fv-uint256-wJ/lean/Fv256/Amd64
for x in "auj UnmarshalJSON0" "auj UnmarshalJa" "auj UnmarshalJc" "auj UnmarshalJd" "auj UnmarshalJq" "auj UnmarshalJSON" "auj UnmarshalJSONHsfd" "auj UnmarshalJSONMain" "aut UnmarshalTextMain" "afd FromDecimal" "afd FromDecimalHsfd" "afd FromDecimalMain" "amfd MustFromDecimal" "amfd MustFromDecimalHsfd" "amfd MustFromDecimalMain"; do
  set -- $x; f=$2; s=$(date +%s)
  HEAVY_PRIORITY=0 /srv/janus-ops/bin/heavy-run -- /usr/bin/time -v build/lcn.sh $1 $D/$f.lean > logs/c7_$f.log 2>&1
  echo "DONE $f t=$(( $(date +%s)-s )) $(grep LEANRC logs/c7_$f.log) rss_kb=$(grep 'Maximum res' logs/c7_$f.log | awk '{print $NF}')" >> logs/c_chain7.out
  grep -q "LEANRC=0" logs/c7_$f.log || break
done
echo ENDMARK >> logs/c_chain7.out
