#!/bin/bash
# lt.sh [file]: lean-check a file in wf2's kept workspace (read-only use), cwd ws root
export PATH=$PATH:/root/.elan/bin LEAN_NUM_THREADS=4
WS=/srv/fv-uint256-wfn/build/ws
cd $WS/root
F=${1:-/srv/fv-uint256-wfn/lean/Fv256/Amd64/FormatNil.lean}
memcap -m 16G lake env lean $F 2>&1 | cut -c1-${W:-600} | head -${L:-120}
echo ENDMARK
