#!/bin/bash
export PATH=$PATH:/usr/local/go/bin
W=$(cat /srv/fv-uint256-wh/build/W2)
cp /srv/fv-uint256-wh/scratch/DivModLibProf.lean $W/root/Fv256/Arm64/DivModLibProf.lean
cd $W/root
/usr/bin/time -v memcap -m 80G lake env lean -o /tmp/claude-0/scratch-null.olean Fv256/Arm64/DivModLibProf.lean > /srv/fv-uint256-wh/build/prof2.out 2>&1
