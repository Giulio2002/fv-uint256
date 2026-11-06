#!/bin/bash
export PATH=$PATH:/usr/local/go/bin
W=$(cat /srv/fv-uint256-wh/build/W2)
cd $W/root
cp /srv/fv-uint256-wh/scratch/DivModLibProfT.lean $W/root/Fv256/Arm64/DivModLibProfT.lean
/usr/bin/time -v memcap -m 60G lake env lean -o /tmp/claude-0/scratch-null.olean Fv256/Arm64/DivModLibProfT.lean > /srv/fv-uint256-wh/build/prof4.out 2>&1
