#!/bin/bash
# genb.sh isa Fn op tail sym
cd /srv/fv-uint256
I=$1; D=$(echo ${I:0:1}|tr a-z A-Z)${I:1}
python3 -I build/gen/bin3b_$I.py "${@:2}" > lean/Fv256/$D/$2.lean
