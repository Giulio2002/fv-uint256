#!/usr/bin/env bash
for t in "arm64 ReverseBytes" "arm64 IMul" "arm64 ILsh" "arm64 IRsh"; do /srv/fv-uint256-wd/wip-d/ver.sh $t; done
touch /srv/fv-uint256-wd/wip-d/batch3.done
