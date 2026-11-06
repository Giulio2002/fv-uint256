#!/bin/bash
export PATH=$PATH:/usr/local/go/bin JANUS_CACHE_DIR=/srv/janus-ops/jcache-shared LEAN_NUM_THREADS=8 JANUS_JOBS=2
cd /srv/fv-uint256-wh
time timeout 7000 memcap -m 40G /srv/janus-wh-pin/bin/janus verify build/ex-arm64-SDiv --proof lean/Fv256/Arm64/SDiv.lean --proof-root lean --theorem Fv256.Arm64.SDiv.correctness --theorem Fv256.Arm64.SDiv.Witness.nonvacuous --full-errors --keep-workspace
