#!/bin/bash
# usage: v.sh ISA FN   (logs to build/log-ISA-FN)
export PATH=$PATH:/usr/local/go/bin LEAN_NUM_THREADS=4 JANUS_JOBS=2
cd /srv/fv-uint256
J=/srv/janus-fv-uint256-janus2/bin/janus
I=$1; F=$2; D=$(echo ${I:0:1}|tr a-z A-Z)${I:1}
[ -f build/ex-$I-$F/identity.json ] || $J extract build/harness-$I "github.com/holiman/uint256.(*Int).$F" build/ex-$I-$F >/dev/null 2>&1
timeout 1800 memcap $J verify build/ex-$I-$F --proof lean/Fv256/$D/$F.lean --proof-root lean --theorem Fv256.$D.$F.correctness
