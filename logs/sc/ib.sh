#!/bin/bash
cd /srv/fv-uint256-wsc/lean
export LEAN_NUM_THREADS=8 JANUS_JOBS=2
HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- timeout 7200 memcap -m 32G lake build Fv256.IbsA Fv256.IbsAWit
echo ENDMARK rc=$?
