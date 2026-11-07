#!/bin/bash
export PATH=$PATH:/usr/local/go/bin JANUS_CACHE_DIR=/srv/fv-uint256-wr/jcache LEAN_NUM_THREADS=8 JANUS_JOBS=2
cd /srv/fv-uint256-wr
time timeout 7000 memcap -m 40G /srv/janus-wr-pin/bin/janus verify build/ex-amd64-EncodeRLP --proof lean-audit/Fv256/Amd64/EncodeRLP.lean --proof-root lean-audit --theorem Fv256.Amd64.EncodeRLP.correctness --full-errors
echo ENDMARK
