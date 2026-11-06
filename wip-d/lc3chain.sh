#!/usr/bin/env bash
cd /srv/fv-uint256-wd
echo $$ > wip-d/lc3.pid
HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- bash wip-d/lc3.sh "$@" > wip-d/logs/lc3chain.log 2>&1
echo "ENDMARK $(date +%T)" >> wip-d/logs/lc3chain.log
