#!/usr/bin/env bash
for f in ISDiv ISMod IDiv IMod; do /srv/fv-uint256-wd/wip-d/ver.sh amd64 $f; done
touch /srv/fv-uint256-wd/wip-d/b23.done
