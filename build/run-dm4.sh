#!/bin/bash
cd /srv/fv-uint256-wB
s=$(date +%s)
timeout 2400 memcap tools-local/lean1d.sh amd64 DivMod DivMod 2300 > build/dm4.log 2>&1
echo "elapsed $(( $(date +%s) - s )) s" >> build/dm4.log
touch build/dm4.done
