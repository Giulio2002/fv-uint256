#!/bin/bash
export PATH=$PATH:/usr/local/go/bin JANUS_CACHE_DIR=/srv/janus-ops/jcache-n10 LEAN_NUM_THREADS=8 JANUS_JOBS=2
cd /srv/fv-uint256-wJ
J=/srv/janus-integ-n10/bin/janus
until grep -q ENDMARK logs/c_chain3.out || ! kill -0 3069240 2>/dev/null; do sleep 20; done
run() { s=$(date +%s)
  HEAVY_PRIORITY=0 /srv/janus-ops/bin/heavy-run -- timeout 7200 memcap -m 30G $J verify build/n10/$2 --proof lean/Fv256/Arm64/$3.lean --proof-root lean --theorem Fv256.Arm64.$3.correctness --theorem Fv256.Arm64.$3.Witness.nonvacuous --full-errors > logs/v_$1.log 2>&1
  echo "VERIFY $1 rc=$? t=$(( $(date +%s)-s ))" >> logs/v_arm.out; }
run rfd arm64-FromDecimal FromDecimalMain
run rmfd arm64-MustFromDecimal MustFromDecimalMain
echo ENDMARK >> logs/v_arm.out
