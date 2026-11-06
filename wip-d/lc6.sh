#!/usr/bin/env bash
# usage: lc6.sh Mod1 Mod2 ... ; compile in wip-d/ws/keep-arm64-IAddMod with -o ; stops at first failing module
R=/srv/fv-uint256-wd; W=$R/wip-d/ws/keep-arm64-IAddMod
export LEAN_PATH=$W/janus/.lake/build/lib/lean:$W/root/.lake/build/lib/lean LEAN_NUM_THREADS=8
for m in "$@"; do
  cp $R/lean/Fv256/$m.lean $W/root/Fv256/$m.lean
  echo "== $m"; s=$(date +%s)
  (cd $W/root && memcap -m 30G timeout 7000 /root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean Fv256/$m.lean -o .lake/build/lib/lean/Fv256/$m.olean 2>&1 | grep -v "warning\|^$\|linter\|Hint\|apply\]\|Note\|^  " | cut -c1-400 | head -30)
  echo "time $(( $(date +%s)-s ))"
done
