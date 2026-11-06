#!/bin/bash
# heavy compile wrapper: lh.sh Name logfile
cd /srv/fv-uint256-wh
( HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- timeout 3000 build/lc2.sh $1 > $2 2>&1; echo done >> $2 )
