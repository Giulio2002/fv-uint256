#!/bin/bash
export PATH=$PATH:/usr/local/go/bin JANUS_CACHE_DIR=/srv/janus-ops/jcache-shared LEAN_NUM_THREADS=8 JANUS_JOBS=2
cd /srv/fv-uint256-wh
time timeout 5400 memcap -m 40G /srv/janus-wh-pin3/bin/janus verify build/ex-amd64-IExp --proof lean/Fv256/Amd64/IExp.lean --proof-root lean --theorem Fv256.Amd64.IExp.correctness --theorem Fv256.Amd64.IExp.Witness.nonvacuous --full-errors --keep-workspace
