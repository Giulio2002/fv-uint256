#!/bin/bash
export PATH=$PATH:/usr/local/go/bin JANUS_CACHE_DIR=/srv/janus-ops/jcache-n10 LEAN_NUM_THREADS=8 JANUS_JOBS=2
cd /srv/fv-uint256-wJ
s=$(date +%s)
HEAVY_PRIORITY=0 /srv/janus-ops/bin/heavy-run -- timeout 3000 memcap -m 30G /srv/janus-integ-n10/bin/janus verify build/n10/a-UJ --proof lean/Fv256/Amd64/UnmarshalJSONAudit.lean --proof-root lean --theorem Fv256.Amd64.UnmarshalJSON.correctness --full-errors > logs/audit_uj2.log 2>&1
echo "AUDITUJ rc=$? t=$(( $(date +%s)-s ))" >> logs/audit_uj2.out
echo ENDMARK >> logs/audit_uj2.out
