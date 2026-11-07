#!/bin/bash
cd /srv/fv-uint256-wJ
for m in UnmarshalTextSa UnmarshalTextSx UnmarshalTextSX UnmarshalTextSb UnmarshalTextSc UnmarshalTextS; do
 S=$(date +%s)
 MEMG=30 /usr/bin/time -v -o logs/c8_$m.time build/lcn.sh auj /srv/fv-uint256-wJ/lean/Fv256/Amd64/$m.lean > logs/c8_$m.log 2>&1
 echo "$m t=$(( $(date +%s)-S )) $(grep Maximum logs/c8_$m.time) errs=$(grep -c ' error' logs/c8_$m.log)" >> logs/c8.out
 [ -f build/ol51/Fv256/Amd64/$m.olean ] || { echo "$m FAILED" >> logs/c8.out; break; }
done
echo ENDMARK >> logs/c8.out
