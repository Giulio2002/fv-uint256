#!/bin/bash
export PATH=$PATH:/usr/local/go/bin JANUS_CACHE_DIR=/srv/janus-ops/jcache-shared LEAN_NUM_THREADS=8 JANUS_JOBS=2
cd /srv/fv-uint256-wI6
HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- timeout 7000 memcap /srv/janus-wI6-pin/bin/janus verify build/ex-arm64-UnmarshalText --proof lean/Fv256/Arm64/UnmarshalTextMain.lean --proof-root lean --theorem Fv256.Arm64.UnmarshalTextMain.correctness --theorem Fv256.Arm64.UnmarshalTextMain.Witness.nonvacuous --theorem Fv256.Arm64.UnmarshalTextMain.Witness.hex --full-errors > logs/v_ut.log 2>&1
echo ENDMARK rc=$? >> logs/v_ut.log
