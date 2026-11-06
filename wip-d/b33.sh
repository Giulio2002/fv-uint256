#!/usr/bin/env bash
# re-confirm on pin f8a20f36 (shared cache), one at a time
/srv/fv-uint256-wd/wip-d/ver.sh arm64 Float64
cp /srv/fv-uint256-wd/wip-d/logs/arm64-Float64.log /srv/fv-uint256-wd/wip-d/logs/arm64-Float64-f8a20f36.log
/srv/fv-uint256-wd/wip-d/ver.sh amd64 Float64
cp /srv/fv-uint256-wd/wip-d/logs/amd64-Float64.log /srv/fv-uint256-wd/wip-d/logs/amd64-Float64-f8a20f36.log
/srv/fv-uint256-wd/wip-d/ver.sh amd64 IDiv
cp /srv/fv-uint256-wd/wip-d/logs/amd64-IDiv.log /srv/fv-uint256-wd/wip-d/logs/amd64-IDiv-f8a20f36.log
touch /srv/fv-uint256-wd/wip-d/b33.done
