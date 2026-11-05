#!/usr/bin/env bash
tail --pid=2640713 -f /dev/null
/srv/fv-uint256-wd/wip-d/ver.sh amd64 IDiv
/srv/fv-uint256-wd/wip-d/ver.sh amd64 IMod
touch /srv/fv-uint256-wd/wip-d/batch16.done
