#!/bin/bash
cd /srv/fv-uint256-wJ
HEAVY_PRIORITY=0 /srv/janus-ops/bin/heavy-run -- python3 build/mkol51.py Fv256.Amd64.SfdLink Fv256.Amd64.SfdLib Fv256.Amd64.UnmarshalSpec Fv256.Amd64.UnmarshalHex Fv256.Amd64.UnmarshalDec Fv256.Amd64.UnmarshalDecJ Fv256.Amd64.UnmarshalQ Fv256.Amd64.FromHexLib Fv256.Amd64.SummaryEnsures > logs/mk_sfdlib.out 2>&1
echo ENDMARK >> logs/mk_sfdlib.out
