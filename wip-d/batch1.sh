#!/usr/bin/env bash
for t in "arm64 ISub" "arm64 IAddUint64" "arm64 ISubUint64" "amd64 IAdd" "amd64 ISub" "amd64 IAddUint64" "amd64 ISubUint64"; do /srv/fv-uint256-wd/wip-d/ver.sh $t; done
touch /srv/fv-uint256-wd/wip-d/batch1.done
