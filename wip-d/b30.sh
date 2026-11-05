#!/usr/bin/env bash
while [ ! -f /srv/fv-uint256-wd/wip-d/b27.done ]; do sleep 20; done
/srv/fv-uint256-wd/wip-d/ver2.sh amd64 ISDiv
/srv/fv-uint256-wd/wip-d/ver.sh arm64 Float64
WIT='--theorem Fv256.Amd64.Float64.Witness.nonvacuous' /srv/fv-uint256-wd/wip-d/ver.sh amd64 Float64
touch /srv/fv-uint256-wd/wip-d/b30.done
