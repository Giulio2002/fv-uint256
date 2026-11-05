#!/usr/bin/env bash
tail --pid=2030076 -f /dev/null
for t in "amd64 ReverseBytes" "amd64 IMul" "amd64 ILsh" "amd64 IRsh"; do /srv/fv-uint256-wd/wip-d/ver.sh $t; done
touch /srv/fv-uint256-wd/wip-d/batch4.done
