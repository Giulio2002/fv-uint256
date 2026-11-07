#!/bin/bash
cd /srv/fv-uint256-wI6
HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- python3 build/mkol.py Fv256.Arm64.UnmarshalHexN Fv256.Arm64.UnmarshalJPost Fv256.Arm64.UnmarshalDecJ > logs/rebuild.log 2>&1
for m in Head Bra Brb Brc Brx BrX ""; do
  f=lean/Fv256/Arm64/UnmarshalText$m.lean
  HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- build/lcx.sh aut /srv/fv-uint256-wI6/$f > logs/ut_$m.log 2>&1
  if grep -q "error" logs/ut_$m.log; then echo FAIL $m >> logs/rebuild.log; break; fi
  echo OK $m >> logs/rebuild.log
done
echo ENDMARK >> logs/rebuild.log
