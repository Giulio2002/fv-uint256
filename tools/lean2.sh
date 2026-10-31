#!/bin/bash
# lean2.sh ISA Fn : run lean on a theorem module directly against the newest consumer workspace (needs a prior verify of that ISA/Fn for the matching Extracted)
I=$1; F=$2; D=$(echo ${I:0:1}|tr a-z A-Z)${I:1}
C=/root/.cache/janus/v1/consumer/442f4b5eed8ae9e166ebfa91
W=${3:-$C/$(ls -t $C | grep -v lock | head -1)}
L=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
cd /srv/fv-uint256/lean
LEAN_PATH=$W/janus/.lake/build/lib/lean:/srv/fv-uint256/build/olean LEAN_NUM_THREADS=4 timeout 1500 memcap $L Fv256/$D/$F.lean
