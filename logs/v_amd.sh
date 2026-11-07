#!/bin/bash
export PATH=$PATH:/usr/local/go/bin JANUS_CACHE_DIR=/srv/janus-ops/jcache-n10 LEAN_NUM_THREADS=8 JANUS_JOBS=2
cd /srv/fv-uint256-wJ
run() { # name extraction Main extra-theorems...
  n=$1; ex=$2; m=$3; shift 3
  th="--theorem Fv256.Amd64.$m.correctness --theorem Fv256.Amd64.$m.Witness.nonvacuous"
  for e in "$@"; do th="$th --theorem Fv256.Amd64.$m.Witness.$e"; done
  s=$(date +%s)
  HEAVY_PRIORITY=0 /srv/janus-ops/bin/heavy-run -- timeout 7200 memcap -m 30G /usr/bin/time -v /srv/janus-fvA-pin51d/bin/janus verify build/n10/$ex --proof lean/Fv256/Amd64/$m.lean --proof-root lean $th --full-errors > logs/v_a_$n.log 2>&1
  rc=$?
  echo "ENDMARK rc=$rc t=$(( $(date +%s)-s ))" >> logs/v_a_$n.log
  echo "$n rc=$rc t=$(( $(date +%s)-s ))" >> logs/v_amd.out
  return $rc
}
run fd amd64-FromDecimal FromDecimalMain && run mfd amd64-MustFromDecimal MustFromDecimalMain && run ut a-UT UnmarshalTextMain hex && run uj a-UJ UnmarshalJSONMain unquoted
echo ENDMARK >> logs/v_amd.out
