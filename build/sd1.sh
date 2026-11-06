#!/bin/bash
cd /srv/fv-uint256-wh
for m in DivLemmas DivProg SDivProg DivSum SDivSum; do echo "=== $m"; ( time bash build/lc2.sh $m ) 2>&1 | grep -v "^$\|^user\|^sys"; done
