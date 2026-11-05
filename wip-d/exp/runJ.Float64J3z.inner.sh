#!/usr/bin/env bash
s=$(date +%s)
WIDTH=400 /srv/fv-uint256-wd/wip-d/wscase.sh arm64 Float64 Float64J3z > /srv/fv-uint256-wd/wip-d/exp/Float64J3z.out 2>&1
echo "time=$(($(date +%s)-s))s" >> /srv/fv-uint256-wd/wip-d/exp/Float64J3z.out
