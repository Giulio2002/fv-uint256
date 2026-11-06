#!/bin/bash
# lre.sh ISA : check lean/Fv256/ISA/EncodeRLP.lean in the kept workspace of the last verify (WS in build/ws-ISA.txt)
export PATH=$PATH:/usr/local/go/bin
D=$1; WS=$(cat /srv/fv-uint256-wr/build/ws-$D.txt)
cp /srv/fv-uint256-wr/lean/Fv256/RlpSpec.lean $WS/root/Fv256/RlpSpec.lean
cp /srv/fv-uint256-wr/lean/Fv256/$D/EncodeRLP.lean $WS/root/Fv256/$D/EncodeRLP.lean
cd $WS/root
memcap -m 16G lake env lean Fv256/$D/EncodeRLP.lean 2>&1 | grep -v "deprecated\|unused\|Hint\|Note\|^$" | cut -c1-400
echo ENDMARK
