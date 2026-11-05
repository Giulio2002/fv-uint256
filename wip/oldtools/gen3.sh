#!/bin/bash
# gen3.sh Fn op  -> both ISAs
cd /srv/fv-uint256
python3 -I build/gen/bin3_arm64.py $1 $2 > lean/Fv256/Arm64/$1.lean
python3 -I build/gen/bin3_amd64.py $1 $2 "$(python3 -I build/gen/tail.py $2)" > lean/Fv256/Amd64/$1.lean
