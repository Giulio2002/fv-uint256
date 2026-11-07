#!/bin/bash
# prof.sh NAME : compile lean/Fv256/Amd64/NAME.lean (auj) with timing, log logs/prof_NAME.log
cd /srv/fv-uint256-wJ
s=$(date +%s)
HEAVY_PRIORITY=0 /srv/janus-ops/bin/heavy-run -- /usr/bin/time -v build/lcn.sh auj /srv/fv-uint256-wJ/lean/Fv256/Amd64/$1.lean > logs/prof_$1.log 2>&1
echo "ENDMARK t=$(( $(date +%s)-s ))" >> logs/prof_$1.log
