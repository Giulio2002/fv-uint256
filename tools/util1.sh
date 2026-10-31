#!/bin/bash
# util1.sh: compile Fv256/Spec.lean and Fv256/Util.lean into build/olean (fast iteration on shared lemmas).
# env: FV_ROOT (default: parent of this script), FV_CACHE (janus consumer cache dir, default newest ~/.cache/janus/v1/consumer/*)
FV_ROOT=${FV_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}
C=${FV_CACHE:-$(ls -dt $HOME/.cache/janus/v1/consumer/*/ | head -1)}
JL=$(ls -dt $C/*/janus/.lake/build/lib/lean | head -1)
L=$(command -v lean || echo $HOME/.elan/bin/lean)
MC=""; command -v memcap >/dev/null && MC=memcap
cd "$FV_ROOT/lean"; mkdir -p ../build/olean/Fv256
for m in Spec Util; do LEAN_PATH=$JL:$FV_ROOT/build/olean LEAN_NUM_THREADS=4 timeout 900 $MC $L Fv256/$m.lean -o ../build/olean/Fv256/$m.olean 2>&1 | grep -A12 "error\|sorry" | head -${1:-60}; done
