#!/usr/bin/env bash
tail --pid=2043376 -f /dev/null
for t in "arm64 ILsh" "arm64 IRsh"; do /srv/fv-uint256-wd/wip-d/ver.sh $t; done
touch /srv/fv-uint256-wd/wip-d/batch5.done
