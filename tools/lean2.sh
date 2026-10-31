#!/bin/bash
# usage: lean2.sh ISA Fn [workspace]  run lean directly on a theorem module against the newest janus verify workspace
# (the workspace must come from a previous v.sh of the same function; needs util1.sh to have built build/olean).
# env: FV_ROOT (default: parent of this script), FV_CACHE (janus consumer cache dir, default ~/.cache/janus/v1/consumer/*)
FV_ROOT=${FV_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}
I=$1; F=$2; D=$(echo ${I:0:1}|tr a-z A-Z)${I:1}
C=${FV_CACHE:-$(ls -dt $HOME/.cache/janus/v1/consumer/*/ | head -1)}
W=${3:-$C/$(ls -t $C | grep -v lock | head -1)}
L=$(command -v lean || echo $HOME/.elan/bin/lean)
MC=""; command -v memcap >/dev/null && MC=memcap
cd "$FV_ROOT/lean"
LEAN_PATH=$W/janus/.lake/build/lib/lean:$FV_ROOT/build/olean LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4} timeout 1500 $MC $L Fv256/$D/$F.lean
