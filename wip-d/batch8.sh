#!/usr/bin/env bash
tail --pid=2170878 -f /dev/null
for t in "amd64 ILsh" "amd64 IRsh"; do /srv/fv-uint256-wd/wip-d/ver.sh $t; done
touch /srv/fv-uint256-wd/wip-d/batch8.done
