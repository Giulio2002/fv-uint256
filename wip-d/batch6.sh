#!/usr/bin/env bash
tail --pid=2117606 -f /dev/null
for t in "arm64 ISRsh"; do /srv/fv-uint256-wd/wip-d/ver.sh $t; done
touch /srv/fv-uint256-wd/wip-d/batch6.done
