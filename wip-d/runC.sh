#!/usr/bin/env bash
W=$(grep -m1 "^Kept workspace:" /srv/fv-uint256-wd/wip-d/logs/arm64-Float64.log | sed 's/.*: //'); cd $W/root
rm -f /srv/fv-uint256-wd/wip-d/exp/C.done
cp /srv/fv-uint256-wd/wip-d/exp/${CF:-C.lean} Fv256/Arm64/Float64.lean
LEAN_NUM_THREADS=8 memcap -m 16G lake env lean Fv256/Arm64/Float64.lean > /srv/fv-uint256-wd/wip-d/exp/C.out 2>&1
echo d > /srv/fv-uint256-wd/wip-d/exp/C.done
