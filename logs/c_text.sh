#!/bin/bash
cd /srv/fv-uint256-wJ
s=$(date +%s)
HEAVY_PRIORITY=0 /srv/janus-ops/bin/heavy-run -- build/lcn.sh aut /srv/fv-uint256-wJ/lean/Fv256/Amd64/UnmarshalText.lean > logs/c_text.log 2>&1
echo "ENDMARK rc=$? t=$(( $(date +%s)-s ))" >> logs/c_text.log
