#!/bin/bash
# vre.sh Amd64|Arm64 [extra janus args]
D=$1; shift
I=$(echo $D | tr 'A-Z' 'a-z')
export PATH=$PATH:/usr/local/go/bin JANUS_CACHE_DIR=/srv/fv-uint256-wr/jcache LEAN_NUM_THREADS=8 JANUS_JOBS=2
cd /srv/fv-uint256-wr
time timeout 7000 memcap -m 40G /srv/janus-wr-pin/bin/janus verify build/ex-$I-EncodeRLP --proof lean/Fv256/$D/EncodeRLP.lean --proof-root lean --theorem Fv256.$D.EncodeRLP.correctness "$@" --full-errors --keep-workspace
echo ENDMARK
