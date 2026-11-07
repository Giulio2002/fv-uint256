#!/bin/bash
cd /srv/fv-uint256-wJ
until grep -q ENDMARK logs/ut1.log && [ "$(stat -c %Y logs/ut1.log)" -gt "$(stat -c %Y logs/fhl_chain.sh)" ]; do sleep 30; done
HEAVY_PRIORITY=0 /srv/janus-ops/bin/heavy-run -- bash build/lc77.sh Fv256/Amd64/FromHexLib.lean > logs/fhl.log 2>&1
echo ENDMARK >> logs/fhl.log
