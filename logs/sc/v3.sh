#!/bin/bash
cd /srv/fv-uint256-wsc
export LEAN_NUM_THREADS=8 JANUS_JOBS=2 JANUS_CACHE_DIR=/srv/janus-ops/jcache-shared PATH=$PATH:/usr/local/go/bin
HEAVY_PRIORITY=0 /srv/janus-ops/bin/heavy-run -- timeout 7200 memcap -m 48G ./bin/janus-n10b verify build/ex3-amd64-Scan --proof lean/Fv256/Amd64/Scan.lean --proof-root lean --theorem Fv256.Amd64.Scan.correctness --full-errors
echo ENDMARK rc=$?
