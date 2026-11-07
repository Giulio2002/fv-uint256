#!/bin/bash
cd /srv/fv-uint256-wI6
export PATH=$PATH:/root/.elan/bin:/usr/local/go/bin
export JANUS_CACHE_DIR=/srv/janus-ops/jcache-shared LEAN_NUM_THREADS=8 JANUS_JOBS=2
HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- timeout 7200 memcap -m 30G /srv/janus-wI6-pin/bin/janus verify build/ex-arm64-IsZero --proof lean/Fv256/Arm64/IsZero.lean --proof-root lean --theorem Fv256.Arm64.IsZero.correctness
echo ENDMARK rc=$?
