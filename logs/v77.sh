#!/bin/bash
export PATH=$PATH:/usr/local/go/bin JANUS_CACHE_DIR=/srv/janus-ops/jcache-shared LEAN_NUM_THREADS=8 JANUS_JOBS=2
cd /srv/fv-uint256-wJ
for F in MulModWithReciprocal IMulModWithReciprocal MulMod IMulMod; do
HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- timeout 5400 memcap /srv/janus-fvA-pin77f/bin/janus verify build/ex-arm64-$F --proof lean/Fv256/Arm64/$F.lean --proof-root lean --theorem Fv256.Arm64.$F.correctness --theorem Fv256.Arm64.$F.Witness.nonvacuous --full-errors --keep-workspace > logs/v77_$F.log 2>&1
echo "$F EXIT=$?" >> logs/v77.done
done
