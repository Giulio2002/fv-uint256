#!/bin/bash
# lre.sh Amd64/File.lean [scratchfile-instead]: sync lean/Fv256 -> workspace, build FormatFastDefs, lean the file
export PATH=$PATH:/usr/local/go/bin LEAN_NUM_THREADS=4
WS=$(cat /srv/fv-uint256-wf2/build/ws-Amd64.txt)
cp /srv/fv-uint256-wf2/lean/Fv256/FormatFast*.lean $WS/root/Fv256/
cp /srv/fv-uint256-wf2/lean/Fv256/Amd64/FormatFast*.lean $WS/root/Fv256/Amd64/ 2>/dev/null
mkdir -p $WS/root/Fv256/Amd64/FM; cp /srv/fv-uint256-wf2/lean/Fv256/Amd64/FM/*.lean $WS/root/Fv256/Amd64/FM/ 2>/dev/null
cd $WS/root
F=${1}
for m in ${PRE}; do memcap -m 16G lake build --no-ansi $m 2>&1 | grep -E "error|warning: declaration" | head -20; done
memcap -m 16G lake env lean $F 2>&1 | cut -c1-400 | head -${LINES_MAX:-150}
echo ENDMARK
