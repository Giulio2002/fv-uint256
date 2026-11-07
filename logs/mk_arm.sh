#!/bin/bash
cd /srv/fv-uint256-wJ
HEAVY_PRIORITY=0 /srv/janus-ops/bin/heavy-run -- python3 build/mkol51.py Fv256.Arm64.SfdTopD Fv256.Arm64.SfdLink Fv256.Arm64.SummaryEnsures Fv256.Arm64.SfdPw > logs/mk_arm.log 2>&1
echo ENDMARK >> logs/mk_arm.log
