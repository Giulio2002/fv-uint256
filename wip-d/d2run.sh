#!/usr/bin/env bash
cd /srv/fv-uint256-wd
echo $$ > wip-d/d2.pid
bash wip-d/ver5.sh "$@"
echo "ENDMARK $1 $2 $(date +%T)" >> wip-d/logs/$1-$2.log
