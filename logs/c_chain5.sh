#!/bin/bash
cd /srv/fv-uint256-wJ
for x in "auj UnmarshalTextSx" "auj UnmarshalTextSX" "auj UnmarshalTextSb" "auj UnmarshalTextSc" "auj UnmarshalTextS" "aut UnmarshalText" "aut UnmarshalHexDisch"; do
  set -- $x; f=$2
  s=$(date +%s)
  HEAVY_PRIORITY=0 /srv/janus-ops/bin/heavy-run -- /usr/bin/time -v build/lcn.sh $1 /srv/fv-uint256-wJ/lean/Fv256/Amd64/$f.lean > logs/c5_$f.log 2>&1
  echo "DONE $f t=$(( $(date +%s)-s )) $(grep LEANRC logs/c5_$f.log) rss_kb=$(grep 'Maximum res' logs/c5_$f.log | awk '{print $NF}')" >> logs/c_chain5.out
  grep -q "LEANRC=0" logs/c5_$f.log || break
done
echo ENDMARK >> logs/c_chain5.out
