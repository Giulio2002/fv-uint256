#!/usr/bin/env bash
cd /srv/fv-uint256-wd
echo $$ > wip-d/d2.pid
bash wip-d/ver5.sh "$@"
# copy any kept workspace for safety
W=$(grep -o "/srv/janus-ops/jcache-shared/v1/consumer/[0-9a-f/]*" wip-d/logs/$1-$2.log | head -1)
[ -n "$W" ] && [ -d "$W" ] && [ ! -d wip-d/ws/keep-$1-$2 ] && cp -a "$W" wip-d/ws/keep-$1-$2
echo "ENDMARK $1 $2 $(date +%T)" >> wip-d/logs/$1-$2.log
