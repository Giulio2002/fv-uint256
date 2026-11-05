#!/bin/bash
# batch.sh "isa Fn" ... ; runs sequentially, prints one-line result each
cd /srv/fv-uint256
for p in "$@"; do set -- $p; build/v.sh $1 $2 > build/log-$1-$2 2>&1; if grep -q "^Verified" build/log-$1-$2; then echo "OK   $1 $2"; else echo "FAIL $1 $2"; fi; done
