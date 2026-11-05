#!/usr/bin/env bash
# usage: ws.sh ISA Fn  -- run lean on lean/Fv256/<D>/<Fn>.lean inside the workspace kept by the last verify of that function
isa=$1; fn=$2; D=$([ $isa = arm64 ] && echo Arm64 || echo Amd64)
W=$(grep -m1 "^Kept workspace:" /srv/fv-uint256-wd/wip-d/logs/$isa-$fn.log | sed 's/.*: //')
cp /srv/fv-uint256-wd/lean/Fv256/$D/$fn.lean $W/root/Fv256/$D/$fn.lean
cd $W/root && LEAN_NUM_THREADS=8 memcap -m 16G lake env lean Fv256/$D/$fn.lean 2>&1 | cut -c1-${WIDTH:-400}
