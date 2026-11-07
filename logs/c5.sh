#!/bin/bash
cd /srv/fv-uint256-wJ
S=$(date +%s)
MEMG=60 /usr/bin/time -v -o logs/c5.time build/lcn.sh auj /srv/fv-uint256-wJ/lean/Fv256/Amd64/UnmarshalTextSxP.lean > logs/c5.log 2>&1
echo "t=$(( $(date +%s)-S )) $(grep Maximum logs/c5.time)" >> logs/c5.out
echo ENDMARK >> logs/c5.out
