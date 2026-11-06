#!/bin/bash
# lisq.sh : check lean/Fv256/Arm64/ISqrt.lean in the ISqrt workspace (no -o)
export PATH=$PATH:/usr/local/go/bin
WS=/srv/janus-ops/jcache-shared/v1/consumer/22911f2cdbd3defee197aa02/7a7fa76c088d4cddf796f7a1
cp /srv/fv-uint256-wh/lean/Fv256/Arm64/ISqrt.lean $WS/root/Fv256/Arm64/ISqrt.lean
cd $WS/root
memcap -m 16G lake env lean Fv256/Arm64/ISqrt.lean 2>&1 | grep -v "deprecated" | cut -c1-400
