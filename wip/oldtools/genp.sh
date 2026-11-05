#!/bin/bash
# genp.sh isa Fn op wval [tail] [doc]
cd /srv/fv-uint256
I=$1; D=$(echo ${I:0:1}|tr a-z A-Z)${I:1}
python3 -I build/gen/pred2.py "$@" > lean/Fv256/$D/$2.lean
