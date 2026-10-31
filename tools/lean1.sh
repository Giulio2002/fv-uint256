#!/bin/bash
# lean1.sh isa Fn : run lean directly on a theorem module (fast iteration; no audit). Needs a prior janus verify log for the workspace path.
I=$1; F=$2; D=$(echo ${I:0:1}|tr a-z A-Z)${I:1}
WS=$(grep -ho "LEAN_PATH=[^ ]*" /srv/fv-uint256/build/log-$I-$F | head -1 | sed 's/LEAN_PATH=//' | cut -d: -f1)
L=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
cd /srv/fv-uint256/lean
mkdir -p ../build/olean/Fv256
for m in Spec Util; do LEAN_PATH=$WS:/srv/fv-uint256/build/olean $L Fv256/$m.lean -o ../build/olean/Fv256/$m.olean 2>&1 | grep -A5 "error" ; done
LEAN_PATH=$WS:/srv/fv-uint256/build/olean timeout 600 memcap $L Fv256/$D/$F.lean 2>&1 | grep -v "warning\|^$\|^Note\|^Hint\|apply\]\|^  [A-Za-z.]*$" | sed 's/Janus.Arm64.Memory.//g'
