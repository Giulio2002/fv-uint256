#!/usr/bin/env bash
# usage: lc5.sh Module(e.g. Arm64/IAddMod) -- compile in ws2 (no -o)
W=/srv/fv-uint256-wd/wip-d/ws/keep-arm64-IAddMod
cp /srv/fv-uint256-wd/lean/Fv256/$1.lean $W/root/Fv256/$1.lean
cd $W/root; export LEAN_PATH=$W/janus/.lake/build/lib/lean:$W/root/.lake/build/lib/lean LEAN_NUM_THREADS=8
memcap -m 30G timeout 3000 /root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean Fv256/$1.lean 2>&1 | grep -v "warning\|linter\|Hint\|apply\]\|Note" | cut -c1-600 | head -${2:-60}
