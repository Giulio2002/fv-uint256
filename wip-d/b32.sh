#!/usr/bin/env bash
while [ ! -f /srv/fv-uint256-wd/wip-d/b31.done ]; do sleep 30; done
/srv/fv-uint256-wd/wip-d/ver.sh amd64 Float64
touch /srv/fv-uint256-wd/wip-d/b32.done
