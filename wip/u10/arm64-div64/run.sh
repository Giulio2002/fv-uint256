#!/bin/bash
# usage: run.sh [FRAMEWORK_LIB_DIR]   default = pinned framework 6639dc84 (Janus 83049110)
# deeprec framework: /root/.cache/janus/v1/framework/de1f0997b092221ed98af24d/.lake/build/lib/lean
FW=${1:-/root/.cache/janus/v1/framework/6639dc849e378aaa97220079/.lake/build/lib/lean}
L=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
cd "$(dirname "$0")"; mkdir -p exo
[ -f exo/Extracted.olean ] || LEAN_PATH=$FW $L ex-arm64-Div/Extracted.lean -o exo/Extracted.olean
time LEAN_NUM_THREADS=2 LEAN_PATH=exo:$FW timeout ${T:-900} $L ${OPTS} Repro.lean 2>&1 | grep -v "^$" | head -60
