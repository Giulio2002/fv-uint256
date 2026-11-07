#!/bin/bash
cd /srv/fv-uint256-wJ
D=/srv/fv-uint256-wJ/lean/Fv256/Amd64
for f in Sa Sx SX Sb Sc S; do
  s=$(date +%s)
  build/lcn.sh auj $D/UnmarshalText$f.lean > logs/c_S$f.log 2>&1
  rc=$(grep LEANRC logs/c_S$f.log)
  echo "DONE $f t=$(( $(date +%s)-s )) errs=$(grep -c 'error' logs/c_S$f.log) $rc" >> logs/c_chain2.out
  grep -q "LEANRC=0" logs/c_S$f.log || break
done
echo ENDMARK >> logs/c_chain2.out
