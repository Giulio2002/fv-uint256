#!/bin/bash
# util1.sh: compile Spec+Util with lean directly (fast iteration on shared lemmas)
JL=$(grep -ho "LEAN_PATH=[^ ]*" /srv/fv-uint256/build/log-amd64-SetUint64 | head -1 | sed 's/LEAN_PATH=//' | cut -d: -f1)
L=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
cd /srv/fv-uint256/lean; mkdir -p ../build/olean/Fv256
for m in Spec Util; do LEAN_PATH=$JL:/srv/fv-uint256/build/olean LEAN_NUM_THREADS=4 timeout 900 memcap $L Fv256/$m.lean -o ../build/olean/Fv256/$m.olean 2>&1 | grep -v "^$" | grep -A12 "error\|sorry" | head -${1:-60}; done
