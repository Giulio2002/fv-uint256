#!/bin/bash
cd /srv/fv-uint256-wh
for m in DivModProg DivModLib; do echo "=== $m"; ( time timeout 4000 bash build/lc2.sh $m ) 2>&1 | grep -v "^$\|^user\|^sys\|linter\|Hint\|apply\|^Note"; done
