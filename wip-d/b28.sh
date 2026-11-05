#!/usr/bin/env bash
while [ ! -f /srv/fv-uint256-wd/wip-d/b27.done ]; do sleep 20; done
sed -i 's|^snap=.*||' /dev/null
/srv/fv-uint256-wd/wip-d/ver.sh arm64 Float64
touch /srv/fv-uint256-wd/wip-d/b28.done
