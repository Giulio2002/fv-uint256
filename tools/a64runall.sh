#!/bin/bash
# runs a64seg.py seg A B for consecutive cuts; logs per segment
cd /srv/fv-uint256-wB5
CUTS="$@"
prev=""
for c in $CUTS; do
  if [ -n "$prev" ]; then
    s=$(date +%s)
    MAXOUT=3000 python3 tools/a64gen.py seg $prev $c > build/a64seg_${prev}_${c}.log 2>&1
    e=$(date +%s)
    echo "$prev $c $((e-s))s $(head -c 60 build/a64seg_${prev}_${c}.log | head -1)" >> build/a64runall.log
  fi
  prev=$c
done
echo DONE >> build/a64runall.log
