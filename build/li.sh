#!/bin/bash
# li.sh Name : check lean/Fv256/Arm64/Name.lean in the IExp workspace (no -o)
export PATH=$PATH:/usr/local/go/bin
source /srv/fv-uint256-wh/build/ws-iexp.env
N=$1
cp /srv/fv-uint256-wh/lean/Fv256/$N.lean $WS2/root/Fv256/$N.lean
cd $WS2/root
memcap -m 16G lake env lean Fv256/$N.lean 2>&1 | grep -v "deprecated" | cut -c1-400
