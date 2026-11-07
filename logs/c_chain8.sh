#!/bin/bash
cd /srv/fv-uint256-wJ
D=/srv/fv-uint256-wJ/lean/Fv256/Amd64
for x in "aut AUtWitA" "aut AUtWitB" "aut AUtWitC" "aut UnmarshalTextMain" "auj AUjWitA" "auj AUjWitB" "auj AUjWitC" "auj UnmarshalJSONMain" "afd FromDecimal" "afd FromDecimalHsfd" "afd AFdWitA" "afd AFdWitB" "afd AFdWitC" "afd FromDecimalMain" "amfd MustFromDecimal" "amfd MustFromDecimalHsfd" "amfd AMFdWitA" "amfd AMFdWitB" "amfd AMFdWitC" "amfd MustFromDecimalMain"; do
  set -- $x; f=$2; s=$(date +%s)
  HEAVY_PRIORITY=0 /srv/janus-ops/bin/heavy-run -- /usr/bin/time -v build/lcn.sh $1 $D/$f.lean > logs/c8_$f.log 2>&1
  echo "DONE $f t=$(( $(date +%s)-s )) $(grep LEANRC logs/c8_$f.log) rss_kb=$(grep 'Maximum res' logs/c8_$f.log | awk '{print $NF}')" >> logs/c_chain8.out
  grep -q "LEANRC=0" logs/c8_$f.log || break
done
echo ENDMARK >> logs/c_chain8.out
