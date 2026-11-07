#!/bin/bash
cd /srv/fv-uint256-wf
for F in MulMod MulModWithReciprocal IMulMod IMulModWithReciprocal; do
  TMO=7200 HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- ./scratch/v77.sh $F > scratch/w_$F.out 2>&1
done
echo END > scratch/v77all.end
