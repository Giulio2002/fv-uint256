#!/usr/bin/env bash
# usage: d2run.sh ISA Fn  (WIT= for stub) ; writes ENDMARK line at the end
cd /srv/fv-uint256-wd
bash wip-d/ver5.sh "$@"
echo "ENDMARK $1 $2 $(date +%T)" >> wip-d/logs/$1-$2.log
