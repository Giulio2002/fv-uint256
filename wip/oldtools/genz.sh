#!/bin/bash
# genz.sh isa Fn op wexpr tail
cd /srv/fv-uint256
I=$1; D=$(echo ${I:0:1}|tr a-z A-Z)${I:1}
python3 -I build/gen/unz.py "$@" > lean/Fv256/$D/$2.lean
