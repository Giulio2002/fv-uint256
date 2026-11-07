#!/bin/bash
cd /srv/fv-uint256-wJ
S=$(date +%s)
MEMG=60 /usr/bin/time -v -o logs/c7.time build/lcn.sh auj /srv/fv-uint256-wJ/lean/Fv256/Amd64/UnmarshalTextSxQ.lean > logs/c7.log 2>&1
echo "t=$(( $(date +%s)-S )) $(grep Maximum logs/c7.time)" >> logs/c7.out
echo ENDMARK >> logs/c7.out
