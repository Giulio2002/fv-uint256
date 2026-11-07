#!/bin/bash
cd /srv/fv-uint256-wJ
s=$(date +%s)
HEAVY_PRIORITY=0 /srv/janus-ops/bin/heavy-run -- build/lcn.sh aut /srv/fv-uint256-wJ/lean/Fv256/Amd64/UnmarshalTextEx.lean > logs/c_Ex2.log 2>&1
echo "ENDMARK t=$(( $(date +%s)-s ))" >> logs/c_Ex2.log
