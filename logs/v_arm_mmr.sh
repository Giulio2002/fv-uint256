#!/bin/bash
export PATH=$PATH:/usr/local/go/bin JANUS_CACHE_DIR=/srv/janus-ops/jcache-shared LEAN_NUM_THREADS=8 JANUS_JOBS=2
cd /srv/fv-uint256-wJ
HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- timeout 5400 memcap /srv/janus-fvA-pin655/bin/janus verify build/ex-arm64-MulModWithReciprocal --proof lean/Fv256/Arm64/MulModWithReciprocal.lean --proof-root lean --theorem Fv256.Arm64.MulModWithReciprocal.correctness --theorem Fv256.Arm64.MulModWithReciprocal.Witness.nonvacuous --full-errors --keep-workspace
echo EXIT=$?
