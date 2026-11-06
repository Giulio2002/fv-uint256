#!/bin/bash
# ExpProg = Exp + squared + Mul segments (+ rodata), from the Exp and IExp extractions of the same harness
cd /srv/fv-uint256-wf
python3 tools/gen_libprog.py lean/Fv256/ExpProg.lean Fv256.ExpProg --fn "github.com/holiman/uint256.(*Int).Exp" --fn "github.com/holiman/uint256.(*Int).squared" --fn "github.com/holiman/uint256.(*Int).Mul" -- build/ex-amd64-Exp/Extracted.lean /srv/fv-uint256-wd/build/ex-amd64-IExp/Extracted.lean
python3 - <<'PY'
import re
p='lean/Fv256/ExpProg.lean'
s=open(p).read()
ex=open('build/ex-amd64-Exp/Extracted.lean').read()
data=re.search(r'def data : List DataSegment := \[.*?\] \}\s*\]',ex,re.S).group(0)
s=s.replace("def program : Amd64.Program := { segments := segments, stubs := stubs, exitAddr := 0, data := [] }",
  data+"\n\ndef program : Amd64.Program := { segments := segments, stubs := stubs, exitAddr := 0, data := data }")
open(p,'w').write(s)
PY
