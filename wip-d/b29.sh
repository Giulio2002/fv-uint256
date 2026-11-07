#!/usr/bin/env bash
while [ ! -f /srv/fv-uint256-wd/wip-d/b28.done ]; do sleep 20; done
WIT=--theorem\ Fv256.Amd64.Float64.Witness.nonvacuous /srv/fv-uint256-wd/wip-d/ver.sh amd64 Float64
touch /srv/fv-uint256-wd/wip-d/b29.done
