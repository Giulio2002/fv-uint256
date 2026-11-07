#!/bin/bash
cd /srv/fv-uint256-wJ
for F in Spec; do :; done
for m in UnmarshalTextS0 UnmarshalTextSxT; do
 S=$(date +%s)
 MEMG=60 /usr/bin/time -v -o logs/c4_$m.time build/lcn.sh auj /srv/fv-uint256-wJ/lean/Fv256/Amd64/$m.lean > logs/c4_$m.log 2>&1
 echo "$m t=$(( $(date +%s)-S )) $(grep Maximum logs/c4_$m.time) errs=$(grep -c ' error' logs/c4_$m.log)" >> logs/c4.out
done
echo ENDMARK >> logs/c4.out
