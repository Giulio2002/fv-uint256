#!/bin/bash
# usage: c_one.sh tag file logname
cd /srv/fv-uint256-wJ
s=$(date +%s)
HEAVY_PRIORITY=0 /srv/janus-ops/bin/heavy-run -- build/lcn.sh $1 $2 > logs/$3.log 2>&1
echo "ENDMARK t=$(( $(date +%s)-s ))" >> logs/$3.log
