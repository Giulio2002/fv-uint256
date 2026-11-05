#!/usr/bin/env bash
tail --pid=1921343 -f /dev/null
for t in "arm64 ReverseBytes" "arm64 IMul" "amd64 ReverseBytes"; do /srv/fv-uint256-wd/wip-d/ver.sh $t; done
touch /srv/fv-uint256-wd/wip-d/batch2.done
