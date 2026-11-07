#!/bin/bash
cd /srv/fv-uint256-wJ
until grep -q ENDMARK logs/uts_chain.out 2>/dev/null; do sleep 20; done
python3 build/mkol77.py Fv256.Arm64.FromDecimalSpec > logs/arm_mk.log 2>&1
echo "mk rc=$?" >> logs/arm_chain.out
echo ENDMARK >> logs/arm_chain.out
