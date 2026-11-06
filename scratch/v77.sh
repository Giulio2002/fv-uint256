#!/bin/bash
# usage: v77.sh FN  : one janus verify on the 77fb30cc binary (correctness + witness), JANUS_TIMINGS=1
export JANUS_TIMINGS=1 PATH=$PATH:/usr/local/go/bin JANUS_CACHE_DIR=/srv/fv-uint256-wf/jcache77 LEAN_NUM_THREADS=8 JANUS_JOBS=2
cd /srv/fv-uint256-wf
F=$1; s=$(date +%s)
timeout ${TMO:-5400} memcap /srv/janus-fvA-pin77f/bin/janus verify build/ex-amd64-$F --proof lean/Fv256/Amd64/$F.lean --proof-root lean --theorem Fv256.Amd64.$F.correctness --theorem Fv256.Amd64.$F.Witness.nonvacuous --full-errors
echo "verify exit $? elapsed $(( $(date +%s) - s )) s"
