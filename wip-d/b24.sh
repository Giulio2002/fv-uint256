#!/usr/bin/env bash
for f in IDiv IMod ISDiv ISMod; do WIT= /srv/fv-uint256-wd/wip-d/ver.sh amd64 $f; done
touch /srv/fv-uint256-wd/wip-d/b24.done
