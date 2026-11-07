#!/bin/bash
cd /srv/fv-uint256-wI6
for m in "$@"; do
  f=lean/Fv256/Arm64/UnmarshalJSON$m.lean
  echo "== $m $(date +%T)"
  HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- build/lcx.sh auj /srv/fv-uint256-wI6/$f > logs/uj_$m.log 2>&1
  if grep -q "error" logs/uj_$m.log; then echo FAIL $m; break; fi
  echo OK $m
done
echo ENDMARK
