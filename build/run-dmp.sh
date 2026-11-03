#!/bin/bash
cd /srv/fv-uint256-wB
s=$(date +%s)
timeout 3000 memcap tools-local/lean1d.sh amd64 DivMod DivModP 2900 > build/dmp.log 2>&1
echo "elapsed $(( $(date +%s) - s )) s" >> build/dmp.log
touch build/dmp.done
