#!/bin/bash
# usage: snapv2.sh ISA(amd64|arm64) ProofFile(rel to lean) logname Theorem...
cd /srv/fv-uint256-we
ISA=$1; EXN=$2; PF=$3; LOG=$4; shift 4
SNAP=build/snap-$LOG
rm -rf $SNAP; mkdir -p $SNAP; cp -r lean $SNAP/lean
TH=""; for t in "$@"; do TH="$TH --theorem $t"; done
export PATH=$PATH:/usr/local/go/bin:/srv/janus-ops/bin:$HOME/.elan/bin
J=/srv/janus-we-p3/bin/janus; export JANUS_CACHE_DIR=/srv/janus-ops/jcache-shared LEAN_NUM_THREADS=8 JANUS_JOBS=2
( time HEAVY_PRIORITY=1 heavy-run -- timeout 7200 memcap $J verify build/ex3-$ISA-$EXN --proof $SNAP/lean/$PF --proof-root $SNAP/lean $TH ) > build/v-$LOG.log 2>&1
echo done > build/v-$LOG.done
