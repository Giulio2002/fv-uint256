#!/usr/bin/env bash
while [ ! -f /srv/fv-uint256-wd/wip-d/b35.done ]; do sleep 30; done
WIT= /srv/fv-uint256-wd/wip-d/ver.sh amd64 IExp
cp /srv/fv-uint256-wd/wip-d/logs/amd64-IExp.log /srv/fv-uint256-wd/wip-d/logs/amd64-IExp-stub.log
touch /srv/fv-uint256-wd/wip-d/b36.done
