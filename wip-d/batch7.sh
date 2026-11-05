#!/usr/bin/env bash
tail --pid=2124568 -f /dev/null
for t in "amd64 ISRsh"; do /srv/fv-uint256-wd/wip-d/ver.sh $t; done
touch /srv/fv-uint256-wd/wip-d/batch7.done
