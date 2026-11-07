#!/bin/bash
cd /srv/fv-uint256-wJ
D=/srv/fv-uint256-wJ/lean/Fv256/Amd64
for f in E0 EA Ex EX Eb Ec ""; do
  s=$(date +%s)
  build/lcn.sh aut $D/UnmarshalText$f.lean > logs/c_Text$f.log 2>&1
  echo "DONE Text$f t=$(( $(date +%s)-s )) $(grep -c 'error' logs/c_Text$f.log) errs $(grep LEANRC logs/c_Text$f.log)" >> logs/c_chain1.out
done
echo ENDMARK >> logs/c_chain1.out
