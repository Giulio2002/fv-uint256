#!/usr/bin/env bash
while [ ! -f /srv/fv-uint256-wd/wip-d/b33.done ]; do sleep 30; done
WIT= /srv/fv-uint256-wd/wip-d/ver.sh amd64 Sqrt
touch /srv/fv-uint256-wd/wip-d/b34.done
