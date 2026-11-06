#!/bin/bash
export PATH=$PATH:/usr/local/go/bin JANUS_CACHE_DIR=/srv/fv-uint256-wh/jcache LEAN_NUM_THREADS=8 JANUS_JOBS=2
cd /srv/fv-uint256-wh
timeout 3300 memcap /srv/janus-wh-pin/bin/janus verify build/ex-arm64-DivMod --proof lean/Fv256/Arm64/DmStub.lean --proof-root lean --theorem Fv256.Arm64.DmStub.correctness --full-errors --keep-workspace
