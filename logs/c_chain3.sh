#!/bin/bash
cd /srv/fv-uint256-wJ
D=/srv/fv-uint256-wJ/lean/Fv256/Amd64
for x in "auj UnmarshalTextS0" "auj UnmarshalTextSa" "auj UnmarshalTextSx" "auj UnmarshalTextSX" "auj UnmarshalTextSb" "auj UnmarshalTextSc" "auj UnmarshalTextS" "aut UnmarshalText" "aut UnmarshalHexDisch" "auj UnmarshalJSON0" "auj UnmarshalJa" "auj UnmarshalJc" "auj UnmarshalJd" "auj UnmarshalJq" "auj UnmarshalJSON"; do
  set -- $x; s=$(date +%s)
  build/lcn.sh $1 $D/$2.lean > logs/c3_$2.log 2>&1
  echo "DONE $2 t=$(( $(date +%s)-s )) $(grep LEANRC logs/c3_$2.log)" >> logs/c_chain3.out
  grep -q "LEANRC=0" logs/c3_$2.log || break
done
echo ENDMARK >> logs/c_chain3.out
