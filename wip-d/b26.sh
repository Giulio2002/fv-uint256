#!/usr/bin/env bash
# wait for the Float64 probe's heavy slot use to finish (ordering by heavy-run queue anyway)
for f in ISDiv ISMod IDiv IMod; do /srv/fv-uint256-wd/wip-d/ver2.sh amd64 $f; done
touch /srv/fv-uint256-wd/wip-d/b26.done
