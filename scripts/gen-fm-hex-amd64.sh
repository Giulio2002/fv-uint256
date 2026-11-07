#!/bin/bash
# Re-targets the amd64 Hex proof at Format's extraction (Hex is the segment at Format+0x1640). Output: Fv256/Amd64/FM/Hex.lean (generated).
# usage: gen-fm-hex-amd64.sh LEAN_DIR
L=${1:-lean}; D=$L/Fv256/Amd64; mkdir -p $D/FM
python3 - "$D/Hex.lean" "$D/FM/Hex.lean" <<'PY'
import sys
s=open(sys.argv[1]).read()
i=s.index('namespace Witness'); j=s.index('end Witness')+len('end Witness')
s=s[:i]+s[j:]
s=s.replace('Extracted.entry','(Extracted.entry + 0x1640)')
s=s.replace('Extracted.program.link impl','(Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).Hex"]).link impl')
s=s.replace('h_data0','h_data4').replace('h_ddisj0_0','h_ddisj0_4')
s=s.replace('namespace Fv256.Amd64.Hex','namespace Fv256.Amd64.FM.Hex').replace('end Fv256.Amd64.Hex','end Fv256.Amd64.FM.Hex')
open(sys.argv[2],'w').write(s)
PY
