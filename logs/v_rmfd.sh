#!/bin/bash
export PATH=$PATH:/usr/local/go/bin JANUS_CACHE_DIR=/srv/janus-ops/jcache-shared LEAN_NUM_THREADS=8 JANUS_JOBS=2
cd /srv/fv-uint256-wJ
s=$(date +%s)
HEAVY_PRIORITY=0 /srv/janus-ops/bin/heavy-run -- timeout 5400 memcap -m 30G /srv/janus-integ-n10/bin/janus verify build/n10/arm64-MustFromDecimal --proof lean/Fv256/Arm64/MustFromDecimalMain.lean --proof-root lean --theorem Fv256.Arm64.MustFromDecimalMain.correctness --full-errors > logs/v_rmfd.log 2>&1
echo "ENDMARK rc=$? t=$(( $(date +%s)-s ))" >> logs/v_rmfd.log
