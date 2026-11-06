#!/usr/bin/env bash
/srv/fv-uint256-wd/wip-d/ver5.sh amd64 Sqrt
cp /srv/fv-uint256-wd/wip-d/logs/amd64-Sqrt.log /srv/fv-uint256-wd/wip-d/logs/amd64-Sqrt-split.log
/srv/fv-uint256-wd/wip-d/ver5.sh amd64 ISqrt
cp /srv/fv-uint256-wd/wip-d/logs/amd64-ISqrt.log /srv/fv-uint256-wd/wip-d/logs/amd64-ISqrt-split.log
touch /srv/fv-uint256-wd/wip-d/b41.done
