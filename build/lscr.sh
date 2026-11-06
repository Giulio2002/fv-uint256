#!/bin/bash
# lscr.sh Name : check scratch/<Name>.lean (module name SqrtBig content) in the Sqrt workspace, 300 s cap, END marker
export PATH=$PATH:/usr/local/go/bin
source /srv/fv-uint256-wh/build/ws-iexp.env
N=$1
cp /srv/fv-uint256-wh/scratch/$N.lean $WS2/root/Fv256/Arm64/Scr$N.lean
cd $WS2/root
( time timeout 300 memcap -m 16G lake env lean Fv256/Arm64/Scr$N.lean ) 2>&1 | grep -v "deprecated\|unused\|Hint\|apply\|Note" | cut -c1-300
echo ENDMARK
