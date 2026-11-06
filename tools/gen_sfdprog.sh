#!/bin/bash
# regenerate lean/Fv256/Arm64/SfdProg.lean (library program of SetFromDecimal's code) from two extractions of one harness binary
cd "$(dirname "$0")/.."
F="github.com/holiman/uint256.(*Int)"
python3 tools/gen_libprog_arm64.py lean/Fv256/Arm64/SfdProg.lean Fv256.Arm64.SfdProg --fn "$F.SetFromDecimal" --fn "$F.fromDecimal" --fn strconv.ParseUint --fn internal/strconv.ParseUint --fn internal/strconv.underscoreOK --fn strconv.toError --fn runtime.decoderune --fn "$F.Mul" --contract runtime.cmpstring --contract runtime.ifaceeq --contract runtime.mallocgc --contract runtime.memmove --contract runtime.newobject --contract runtime.gcWriteBarrier2 --contract runtime.gcWriteBarrier1 --contract runtime.gcWriteBarrier3 --contract runtime.memclrNoHeapPointers -- build/ex-arm64-SetFromDecimal/Extracted.lean build/ex-arm64-FromDecimal/Extracted.lean
