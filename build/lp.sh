#!/bin/bash
# lp.sh Sub/Name... : compile lean/Fv256/<Sub/Name>.lean into the IExp workspace with olean (e.g. SqrtMath, Arm64/Foo)
export PATH=$PATH:/usr/local/go/bin
source /srv/fv-uint256-wh/build/ws-iexp.env
for N in "$@"; do
mkdir -p $WS2/root/Fv256/$(dirname $N) $WS2/root/.lake/build/lib/lean/Fv256/$(dirname $N)
cp /srv/fv-uint256-wh/lean/Fv256/$N.lean $WS2/root/Fv256/$N.lean
cd $WS2/root
memcap -m 16G lake env lean -o .lake/build/lib/lean/Fv256/$N.olean -i .lake/build/lib/lean/Fv256/$N.ilean Fv256/$N.lean 2>&1 | grep -v "deprecated\|unused\|Hint\|apply\|Note\|^$" | cut -c1-300
done
