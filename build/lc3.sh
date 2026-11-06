#!/bin/bash
# lc3.sh Name : compile lean/Fv256/Arm64/Name.lean in workspace $WS (arg 2 optional)
export PATH=$PATH:/usr/local/go/bin
W=${WS:-$(cat /srv/fv-uint256-wh/build/W2)}
N=$1
mkdir -p $W/root/Fv256/Arm64 $W/root/.lake/build/lib/lean/Fv256/Arm64
cp /srv/fv-uint256-wh/lean/Fv256/Arm64/$N.lean $W/root/Fv256/Arm64/$N.lean
cd $W/root
memcap -m 16G lake env lean -o .lake/build/lib/lean/Fv256/Arm64/$N.olean -i .lake/build/lib/lean/Fv256/Arm64/$N.ilean Fv256/Arm64/$N.lean 2>&1 | grep -v "deprecated" | cut -c1-600
