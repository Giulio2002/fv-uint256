#!/usr/bin/env bash
# usage: lc3.sh Mod1 Mod2 ...  (module names under Fv256.Arm64 etc., e.g. Arm64/AddModEntry): sync from lean/ into ws1 and compile each to olean, stop at first error
R=/srv/fv-uint256-wd; W=$R/wip-d/ws/ws1
export LEAN_PATH=$W/janus/.lake/build/lib/lean:$W/root/.lake/build/lib/lean
export LEAN_NUM_THREADS=8
for m in "$@"; do
  cp $R/lean/Fv256/$m.lean $W/root/Fv256/$m.lean
  mkdir -p $W/root/.lake/build/lib/lean/Fv256/$(dirname $m)
  echo "== $m"; s=$(date +%s)
  (cd $W/root && memcap -m 30G timeout 7000 /root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean Fv256/$m.lean -o .lake/build/lib/lean/Fv256/$m.olean 2>&1 | grep -v "warning\|^$\|linter\|Hint\|apply\]\|Note" | head -40)
  echo "time $(( $(date +%s)-s ))"
done
