#!/usr/bin/env bash
tail --pid=2403720 -f /dev/null
WIT= /srv/fv-uint256-wd/wip-d/ver.sh amd64 SetBytes
WIT= /srv/fv-uint256-wd/wip-d/ver.sh amd64 IDiv
touch /srv/fv-uint256-wd/wip-d/batch13.done
