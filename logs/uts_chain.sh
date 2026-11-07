#!/bin/bash
cd /srv/fv-uint256-wJ
run() { # tag name
  S=$(date +%s)
  /usr/bin/time -v -o logs/c_$2.time build/lcx.sh $1 /srv/fv-uint256-wJ/lean/Fv256/Amd64/$2.lean > logs/c_$2.log 2>&1
  echo "$2 t=$(( $(date +%s)-S )) $(grep Maximum logs/c_$2.time) errs=$(grep -c 'error' logs/c_$2.log)" >> logs/uts_chain.out
  [ -f build/ol77/Fv256/Amd64/$2.olean ] || { echo "$2 FAILED" >> logs/uts_chain.out; return 1; }
}
rm -f build/ol77/Fv256/Amd64/UnmarshalSpec.olean
run uj UnmarshalSpec || exit
for F in S0 Sa Sx SX Sb Sc S; do run uj UnmarshalText$F || break; done
echo ENDMARK >> logs/uts_chain.out
