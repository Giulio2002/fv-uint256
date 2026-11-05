#!/usr/bin/env bash
tail --pid=2783757 -f /dev/null
/srv/fv-uint256-wd/wip-d/ver.sh arm64 SetBytes
/srv/fv-uint256-wd/wip-d/ver.sh amd64 SetBytes
touch /srv/fv-uint256-wd/wip-d/batch17.done
