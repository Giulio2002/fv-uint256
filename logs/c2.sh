#!/bin/bash
cd /srv/fv-uint256-wJ
for t in "afd lean/Fv256/Arm64/FromDecimal.lean" "amfd lean/Fv256/Arm64/MustFromDecimal.lean"; do
 set -- $t; S=$(date +%s)
 /usr/bin/time -v -o logs/c2_$1.time build/lcx.sh $1 /srv/fv-uint256-wJ/$2 > logs/c2_$1.log 2>&1
 echo "$1 t=$(( $(date +%s)-S )) $(grep Maximum logs/c2_$1.time) errs=$(grep -c ' error' logs/c2_$1.log)" >> logs/c2.out
done
echo ENDMARK >> logs/c2.out
