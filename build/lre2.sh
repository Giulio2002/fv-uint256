#!/bin/bash
# lre2.sh Mod... : copy RlpSpec + Amd64/Erlp*.lean into the kept workspace and `lake build` the given modules
export PATH=$PATH:/usr/local/go/bin
WS=$(cat /srv/fv-uint256-wr/build/ws-Amd64.txt)
OUT=/srv/fv-uint256-wr/build/lre2.out
cp /srv/fv-uint256-wr/lean/Fv256/Rlp*.lean $WS/root/Fv256/
cp /srv/fv-uint256-wr/lean/Fv256/Amd64/Erlp*.lean $WS/root/Fv256/Amd64/
cd $WS/root
memcap -m 16G lake build --no-ansi "$@" > $OUT 2>&1
grep -n "error: Fv256/Amd64/Erlp\|declaration uses" $OUT | cut -c1-200
awk '/error: Fv256\/Amd64\/Erlp|^case h|^⊢/{f=1} f' $OUT | head -${LINES_MAX:-120} | cut -c1-300
echo ENDMARK
