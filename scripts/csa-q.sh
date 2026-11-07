#!/usr/bin/env bash
# csa-q.sh ISA FN [audit|full]   -- serialised (flock) STUB audit / full verify of one row; prints a verdict.
# One heavy Lean job at a time across all FV-CSA agents. Output slice: /srv/fv-uint256-csa-aud/q/ISA-FN-MODE.out
# Usage (background):  scripts/csa-q.sh arm64 Hex audit > /dev/null 2>&1 &   then read q/arm64-Hex-audit.out (VERDICT line last)
isa=$1; fn=$2; mode=${3:-audit}
Q=/srv/fv-uint256-csa-aud; mkdir -p $Q/q; out=$Q/q/$isa-$fn-$mode.out
cd /srv/fv-uint256-csa
{
exec 9>$Q/.q.lock
flock 9
[ -f $Q/.waitpid ] && while kill -0 "$(cat $Q/.waitpid)" 2>/dev/null; do sleep 10; done
while :; do
  l=$(cut -d' ' -f1 /proc/loadavg | cut -d. -f1); m=$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo); d=$(df --output=avail -BG / | tail -1 | tr -dc 0-9)
  [ "$l" -le 62 ] && [ "$m" -ge 60 ] && [ "$d" -ge 70 ] && break
  echo "waiting load=$l mem=$m disk=$d"; sleep 30
done
log=$Q/build/log-$isa-$fn; sz=$( [ -f $log ] && stat -c %s $log || echo 0 )
rm -rf $Q/build/ex-$isa-$fn-nope
[ $mode = audit ] && export STUB=1
HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- timeout 3400 scripts/csa-row.sh $isa $fn $mode > $out.raw 2>&1
tail -c +$((sz+1)) $log > $out.log 2>/dev/null
python3 scripts/csa-verdict.py $out.log $mode > $out 2>&1; cat $out.raw | grep ENDMARK >> $out
}
