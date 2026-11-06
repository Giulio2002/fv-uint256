#!/usr/bin/env bash
cd /srv/fv-uint256-wd
echo $$ > wip-d/lc6.pid
HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- bash wip-d/lc6.sh "$@" > wip-d/logs/lc6chain.log 2>&1
echo "ENDMARK $(date +%T)" >> wip-d/logs/lc6chain.log
