#!/bin/bash
# gen1.sh isa Fn post ret tail doc
cd /srv/fv-uint256
I=$1; D=$(echo ${I:0:1}|tr a-z A-Z)${I:1}
python3 -I build/gen/un1.py "$@" > lean/Fv256/$D/$2.lean
