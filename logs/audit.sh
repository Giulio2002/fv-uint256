#!/bin/bash
export PATH=$PATH:/usr/local/go/bin JANUS_CACHE_DIR=/srv/janus-ops/jcache-shared LEAN_NUM_THREADS=8 JANUS_JOBS=2
cd /srv/fv-uint256-wJ
J=/srv/janus-integ-n10/bin/janus
run() { # name extraction file theorem
  s=$(date +%s)
  timeout 3000 memcap -m 30G $J verify build/n10/$2 --proof lean/Fv256/$3.lean --proof-root lean --theorem $4 --full-errors > logs/audit_$1.log 2>&1
  echo "AUDIT $1 rc=$? t=$(( $(date +%s)-s ))" >> logs/audit.out
}
run ut a-UT Amd64/UnmarshalTextAudit Fv256.Amd64.UnmarshalText.correctness
run uj a-UJ Amd64/UnmarshalJSONAudit Fv256.Amd64.UnmarshalJSON.correctness
run afd amd64-FromDecimal Amd64/FromDecimalAudit Fv256.Amd64.FromDecimal.correctness
run amfd amd64-MustFromDecimal Amd64/MustFromDecimalAudit Fv256.Amd64.MustFromDecimal.correctness
run rfd arm64-FromDecimal Arm64/FromDecimalAudit Fv256.Arm64.FromDecimal.correctness
run rmfd arm64-MustFromDecimal Arm64/MustFromDecimalAudit Fv256.Arm64.MustFromDecimal.correctness
echo ENDMARK >> logs/audit.out
