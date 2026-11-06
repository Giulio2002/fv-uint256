#!/bin/bash
# AddModProg = ModProg + AddMod segment (+ rodata), from two extractions of the same harness (AddMod and IAddMod)
cd /srv/fv-uint256-wf
python3 tools/gen_libprog.py lean/Fv256/AddModProg.lean Fv256.AddModProg --fn "github.com/holiman/uint256.(*Int).AddMod" --base Fv256.ModProg.program -- build/ex-amd64-AddMod/Extracted.lean /srv/fv-uint256-wd/build/ex-amd64-IAddMod/Extracted.lean
python3 - <<'PY'
import re
p='lean/Fv256/AddModProg.lean'
s=open(p).read()
ex=open('build/ex-amd64-AddMod/Extracted.lean').read()
data=re.search(r'def data : List DataSegment := \[.*?\] \}\s*\]',ex,re.S).group(0)
s=s.replace("def program : Amd64.Program := { Fv256.ModProg.program with segments := Fv256.ModProg.segments ++ segments, stubs := Fv256.ModProg.stubs ++ stubs }",
 data+"\n\ndef program : Amd64.Program := { Fv256.ModProg.program with segments := Fv256.ModProg.program.segments ++ segments, stubs := Fv256.ModProg.program.stubs ++ stubs, data := data }")
open(p,'w').write(s)
PY
