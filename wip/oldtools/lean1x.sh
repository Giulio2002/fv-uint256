#!/bin/bash
# lean1x.sh isa Fn File : like lean1 but module file name differs (scratch)
I=$1; F=$2; M=$3; D=$(echo ${I:0:1}|tr a-z A-Z)${I:1}
WS=$(grep -ho "LEAN_PATH=[^ ]*" /srv/fv-uint256/build/log-$I-$F | head -1 | sed 's/LEAN_PATH=//' | cut -d: -f1)
cd /srv/fv-uint256/lean
LEAN_PATH=$WS:/srv/fv-uint256/build/olean timeout ${4:-300} memcap /root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean Fv256/$D/$M.lean 2>&1 | grep -v "warning\|^$\|^Note\|^Hint\|apply\]\|^  [A-Za-z.]*$" | sed 's/Janus.Arm64.Memory.//g'
