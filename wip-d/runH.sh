#!/usr/bin/env bash
# heavy-run wrapper around a kept-workspace lean check (C.lean -> Float64.lean)
cat > /srv/fv-uint256-wd/wip-d/runH.inner.sh <<'IN'
#!/usr/bin/env bash
W=$(grep -m1 "^Kept workspace:" /srv/fv-uint256-wd/wip-d/logs/arm64-Float64.log | sed 's/.*: //'); cd $W/root
cp /srv/fv-uint256-wd/wip-d/exp/${CF:-C.lean} Fv256/Arm64/Float64.lean
LEAN_NUM_THREADS=8 timeout 3000 memcap -m 16G lake env lean Fv256/Arm64/Float64.lean > /srv/fv-uint256-wd/wip-d/exp/C.out 2>&1
echo d > /srv/fv-uint256-wd/wip-d/exp/C.done
IN
chmod +x /srv/fv-uint256-wd/wip-d/runH.inner.sh
rm -f /srv/fv-uint256-wd/wip-d/exp/C.done
HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- /srv/fv-uint256-wd/wip-d/runH.inner.sh
