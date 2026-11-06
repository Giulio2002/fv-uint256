#!/bin/bash
# lihr.sh : check lean/Fv256/Arm64/Hex.lean in the arm64 Hex workspace (no -o)
export PATH=$PATH:/usr/local/go/bin
WS=/srv/janus-ops/jcache-shared/v1/consumer/22911f2cdbd3defee197aa02/6a13dfcf198d52b66ad11035
mkdir -p $WS/root/Fv256/Arm64
cp /srv/fv-uint256-wh/lean/Fv256/Arm64/Hex.lean $WS/root/Fv256/Arm64/Hex.lean
cd $WS/root
memcap -m 16G lake env lean Fv256/Arm64/Hex.lean 2>&1 | grep -v "deprecated\|unused\|Hint\|Note\|^$" | cut -c1-400
echo ENDMARK
