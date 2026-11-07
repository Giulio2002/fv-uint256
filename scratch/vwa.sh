#!/bin/bash
# vw.sh Mod Theorem : janus verify (arm64) keep workspace
M=$1; T=$2; shift; shift
export PATH=$PATH:/usr/local/go/bin:/root/.elan/bin JANUS_CACHE_DIR=/srv/janus-ops/jcache-shared LEAN_NUM_THREADS=8 JANUS_JOBS=2
cd /srv/fv-uint256-wfn
time timeout 5000 memcap -m 40G /srv/janus-wr-pin2/bin/janus verify build/ex2-arm64-Format --proof lean/Fv256/Arm64/$M.lean --proof-root lean --theorem Fv256.Arm64.FormatNil.$T "$@" --full-errors --keep-workspace
echo ENDMARK rc=$?
