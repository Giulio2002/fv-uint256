#!/bin/bash
# usage: vk.sh EXDIR PROOF THEOREM [extra]
export PATH=$PATH:/usr/local/go/bin JANUS_CACHE_DIR=/srv/fv-uint256-wh/jcache LEAN_NUM_THREADS=8 JANUS_JOBS=2
cd /srv/fv-uint256-wh
EX=$1; PF=$2; TH=$3; shift 3
HEAVY_PRIORITY=1 timeout 3300 memcap /srv/janus-wh-pin/bin/janus verify $EX --proof $PF --proof-root lean --theorem $TH "$@"
