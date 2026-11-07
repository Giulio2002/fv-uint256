#!/bin/bash
cd /srv/fv-uint256-wJ
until grep -q ENDMARK logs/c5.out 2>/dev/null; do sleep 10; done
S=$(date +%s)
MEMG=60 /usr/bin/time -v -o logs/c6.time build/lcn.sh auj /srv/fv-uint256-wJ/lean/Fv256/Amd64/UnmarshalTextPr.lean > logs/c6.log 2>&1
echo "t=$(( $(date +%s)-S )) $(grep Maximum logs/c6.time)" >> logs/c6.out
echo ENDMARK >> logs/c6.out
