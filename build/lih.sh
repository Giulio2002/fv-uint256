#!/bin/bash
# lih.sh : check lean/Fv256/Amd64/Hex.lean in the amd64 Hex workspace (no -o)
export PATH=$PATH:/usr/local/go/bin
WS=/srv/janus-ops/jcache-shared/v1/consumer/22911f2cdbd3defee197aa02/fec189886b833a69832bf1b2
cp /srv/fv-uint256-wh/lean/Fv256/Amd64/Hex.lean $WS/root/Fv256/Amd64/Hex.lean
cd $WS/root
memcap -m 16G lake env lean Fv256/Amd64/Hex.lean 2>&1 | grep -v "deprecated\|unused\|Hint\|Note\|^$" | cut -c1-400
echo ENDMARK
