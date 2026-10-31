#!/bin/bash
# usage: lean2.sh ISA Fn [workspace]  run lean directly on a theorem module against the newest janus verify workspace
# (the workspace must come from a previous v.sh of the same function; needs util1.sh to have built build/olean).
# env: FV_ROOT (default: parent of this script), FV_CACHE (janus consumer cache dir, default ~/.cache/janus/v1/consumer/*)
FV_ROOT=${FV_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}
I=$1; F=$2; D=$(echo ${I:0:1}|tr a-z A-Z)${I:1}
C=${FV_CACHE:-$(ls -dt $HOME/.cache/janus/v1/consumer/*/ | head -1)}
W=$3
if [ -z "$W" ]; then
  for d in $(ls -dt $HOME/.cache/janus/v1/consumer/*/*/ 2>/dev/null); do
    o=$d/janus/.lake/build/lib/lean/Extracted.olean
    if grep -qaP "\\(\\*Int\\)\\.$F\\x00" $o 2>/dev/null || grep -qaP "uint256\\.$F\\x00" $o 2>/dev/null; then W=${d%/}; break; fi
  done
fi
[ -n "$W" ] || { echo "no workspace found for $F (run v.sh first)"; exit 2; }
L=$(command -v lean || echo $HOME/.elan/bin/lean)
MC=""; command -v memcap >/dev/null && MC=memcap
cd "$FV_ROOT/lean"
LEAN_PATH=$W/janus/.lake/build/lib/lean:$FV_ROOT/build/olean LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4} timeout 1500 $MC $L Fv256/$D/$F.lean
