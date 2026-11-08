#!/usr/bin/env bash
# rowrun.sh FN [audit|full] : crow2 under heavy-run; on the first "Lean errors" in the log, kill the run tree (own pids) and print the errors; else print the result line.
FN=$1; MODE=${2:-audit}; A=/srv/fv-uint256-csb-aud; cd $A
L=build/log-amd64-$FN; rm -f $L; rm -rf build/ex-amd64-$FN
HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- timeout 5400 ./crow2.sh $FN $MODE > run-$FN.out 2>&1 &
P=$!
desc() { local c; for c in $(pgrep -P $1); do desc $c; echo $c; done; }
while kill -0 $P 2>/dev/null; do
  if grep -q "^Lean errors\|EXTRACT-FAIL\|error: build failed" $L 2>/dev/null; then sleep 3; for q in $(desc $P) $P; do kill $q 2>/dev/null; done; echo "ROWFAIL $FN"; grep -A6 -m12 "error" $L | cut -c1-400 | head -80; exit 1; fi
  sleep 4
done
cat run-$FN.out | cut -c1-200; grep -E "^=== |Invalid|FAIL" $L | cut -c1-300 | head -20
