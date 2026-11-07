#!/bin/bash
cd /srv/fv-uint256-wsc/lean
export LEAN_NUM_THREADS=8 JANUS_JOBS=2 PATH=$PATH:/usr/local/go/bin
HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- timeout 14400 memcap -m 48G lake build Fv256.Amd64.FromDecimalSpec Fv256.SpecScan Fv256.IbsA Fv256.Amd64.MoLib.Top Fv256.Amd64.ExpMain Fv256.Amd64.ExpSum
echo ENDMARK rc=$?
