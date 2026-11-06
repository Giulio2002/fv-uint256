#!/bin/bash
export PATH=$PATH:/usr/local/go/bin
W=$(cat /srv/fv-uint256-wh/build/W2)
cd $W/root
for n in G H; do
cp /srv/fv-uint256-wh/scratch/DivModLibProf$n.lean $W/root/Fv256/Arm64/DivModLibProf$n.lean
/usr/bin/time -v memcap -m 80G lake env lean -o /tmp/claude-0/scratch-null.olean Fv256/Arm64/DivModLibProf$n.lean > /srv/fv-uint256-wh/build/prof3$n.out 2>&1
done
