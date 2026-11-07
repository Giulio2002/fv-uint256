#!/bin/bash
# regenerate lean/Fv256/Arm64/SfdProg.lean (library program of SetFromDecimal's code) from an extraction of the harness binary
# (build/ex-arm64-SetFromDecimal, extracted with the flags below; the same extraction as the final `janus verify`, so that the
# library stubs equal the extraction's stubs).  The generator wants two extractions: the same one twice.
cd "$(dirname "$0")/.."
F="github.com/holiman/uint256.(*Int)"
FL="--contract runtime.cmpstring --contract runtime.ifaceeq --contract runtime.mallocgc --contract runtime.memmove --contract runtime.newobject --contract runtime.gcWriteBarrier2 --contract runtime.gcWriteBarrier1 --contract runtime.gcWriteBarrier3 --contract runtime.growslice --contract runtime.slicebytetostring --contract runtime.concatstring2"
${JANUS:-janus} extract build/harness-arm64 "$F.SetFromDecimal" build/ex-arm64-SetFromDecimal $FL
python3 tools/gen_libprog_arm64.py lean/Fv256/Arm64/SfdProg.lean Fv256.Arm64.SfdProg --fn "$F.SetFromDecimal" --fn "$F.fromDecimal" --fn strconv.ParseUint --fn internal/strconv.ParseUint --fn internal/strconv.underscoreOK --fn strconv.toError --fn runtime.decoderune --fn "$F.Mul" --contract runtime.cmpstring --contract runtime.ifaceeq --contract runtime.mallocgc --contract runtime.memmove --contract runtime.newobject --contract runtime.gcWriteBarrier2 --contract runtime.gcWriteBarrier1 --contract runtime.gcWriteBarrier3 -- build/ex-arm64-SetFromDecimal/Extracted.lean build/ex-arm64-SetFromDecimal/Extracted.lean
