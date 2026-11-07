#!/usr/bin/env bash
while [ ! -f /srv/fv-uint256-wd/wip-d/b30.done ]; do sleep 30; done
for f in ISMod IMod; do /srv/fv-uint256-wd/wip-d/ver3.sh amd64 $f; done
touch /srv/fv-uint256-wd/wip-d/b31.done
