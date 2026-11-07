#!/bin/bash
export PATH=$PATH:/usr/local/go/bin JANUS_CACHE_DIR=/srv/janus-ops/jcache-shared LEAN_NUM_THREADS=8 JANUS_JOBS=2
cd /srv/fv-uint256-wI6
HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- timeout 3000 memcap /srv/janus-wI6-pin/bin/janus verify build/ex-arm64-UnmarshalText --proof lean/Fv256/Arm64/UnmarshalTextAudit.lean --proof-root lean --theorem Fv256.Arm64.UnmarshalTextAudit.correctness --theorem Fv256.Arm64.UnmarshalTextAudit.Witness.nonvacuous --full-errors > logs/audit1.log 2>&1
echo ENDMARK rc=$? >> logs/audit1.log
