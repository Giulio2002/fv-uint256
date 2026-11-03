#!/bin/bash
cd /srv/fv-uint256-wB
s=$(date +%s)
timeout 3000 memcap tools-local/lean1d.sh amd64 DivMod DivMod 2900 > build/dm3.log 2>&1
echo "elapsed $(( $(date +%s) - s )) s" >> build/dm3.log
touch build/dm3.done
