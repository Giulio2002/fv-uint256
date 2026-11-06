#!/bin/bash
cd /srv/fv-uint256-wB7/lean
export PATH=$PATH:/root/.elan/bin:/usr/local/go/bin
( time LEAN_NUM_THREADS=8 memcap -m 40G timeout 3000 lake build "$@" ) > ../build/lb-$1.log 2>&1
echo "ENDMARK rc=$?" >> ../build/lb-$1.log
