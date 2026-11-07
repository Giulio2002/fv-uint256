#!/bin/bash
cd /srv/fv-uint256-wJ
python3 build/mkol51.py Fv256.Amd64.FromDecimalSpec Fv256.Amd64.UnmarshalSpec Fv256.Amd64.UnmarshalDec Fv256.Amd64.UnmarshalDecJ Fv256.Amd64.UnmarshalHex Fv256.Amd64.FromHexLib Fv256.Amd64.SbtsFacts Fv256.Arm64.FromDecimalSpec > logs/c3_mk.log 2>&1
echo "mk rc=$?" >> logs/c3.out
for t in aut auj afd amfd rfd rmfd; do build/lcn.sh $t Extracted > logs/c3_ex_$t.log 2>&1; echo "ex $t rc=$?" >> logs/c3.out; done
for t in "rfd lean/Fv256/Arm64/FromDecimal.lean" "rmfd lean/Fv256/Arm64/MustFromDecimal.lean"; do
 set -- $t; S=$(date +%s)
 /usr/bin/time -v -o logs/c3_$1.time build/lcn.sh $1 /srv/fv-uint256-wJ/$2 > logs/c3_$1.log 2>&1
 echo "$1 t=$(( $(date +%s)-S )) $(grep Maximum logs/c3_$1.time) errs=$(grep -c ' error' logs/c3_$1.log)" >> logs/c3.out
done
echo ENDMARK >> logs/c3.out
