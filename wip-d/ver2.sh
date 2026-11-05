#!/usr/bin/env bash
# usage: ver.sh ISA Fn  -- verifies from a private snapshot of lean/ so edits to lean/ never make the run stale
isa=$1; fn=$2; D=$([ $isa = arm64 ] && echo Arm64 || echo Amd64)
R=/srv/fv-uint256-wd
cd $R
snap=$R/stage/$isa-$fn-cold
rm -rf $snap; mkdir -p $snap/lean
(cd lean && tar cf - --exclude=.lake --exclude=wip . ) | tar xf - -C $snap/lean
cp -a $R/lean/.lake $snap/lean/.lake
[ -n "${OVERLAY:-}" ] && cp -a $OVERLAY/. $snap/lean/
echo "-- cold-probe $(date +%s)" >> $snap/lean/Fv256/$D/$fn.lean
LOG=wip-d/logs/$fn-lib-cold-$isa-$(date +%Y%m%d-%H%M).log
export LEAN_NUM_THREADS=8 JANUS_JOBS=2 JANUS_CACHE_DIR=$R/jcache PATH=$PATH:/usr/local/go/bin
J=/srv/janus-wd-pin/bin/janus
mkdir -p wip-d/logs
s=$(date +%s)
HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- timeout 3000 memcap $J verify build/ex-$isa-$fn --proof $snap/lean/Fv256/$D/$fn.lean --proof-root $snap/lean --full-errors --keep-workspace --theorem Fv256.$D.$fn.correctness ${WIT---theorem Fv256.$D.$fn.Witness.nonvacuous}  > $LOG 2>&1
rm -rf $snap
echo "rc=$? time=$(( $(date +%s)-s ))s" >> $LOG
