#!/bin/bash
# lo.sh Name... : compile Arm64 modules into the IExp workspace (with olean)
export PATH=$PATH:/usr/local/go/bin
source /srv/fv-uint256-wh/build/ws-iexp.env
for N in "$@"; do
cp /srv/fv-uint256-wh/lean/Fv256/Arm64/$N.lean $WS2/root/Fv256/Arm64/$N.lean
cd $WS2/root
memcap -m 16G lake env lean -o .lake/build/lib/lean/Fv256/Arm64/$N.olean -i .lake/build/lib/lean/Fv256/Arm64/$N.ilean Fv256/Arm64/$N.lean 2>&1 | grep -v "deprecated\|unused\|Hint\|apply\|Note\|^$" | cut -c1-300
done
