#!/usr/bin/env bash
# usage: wscase.sh ISA Fn rel...  compile extra modules (e.g. SetBytesDefs, SbCases/Case3) into the kept workspace of ISA/Fn
isa=$1; fn=$2; shift 2; D=$([ $isa = arm64 ] && echo Arm64 || echo Amd64)
W=$(grep -m1 "^Kept workspace:" /srv/fv-uint256-wd/wip-d/logs/$isa-$fn.log | sed 's/.*: //')
cd $W/root
OUT=.lake/build/lib/lean/Fv256/$D
for m in "$@"; do
  mkdir -p Fv256/$D/$(dirname $m) $OUT/$(dirname $m)
  cp /srv/fv-uint256-wd/lean/Fv256/$D/$m.lean Fv256/$D/$m.lean
  LEAN_NUM_THREADS=8 memcap -m 16G lake env lean -o $OUT/$m.olean -i $OUT/$m.ilean Fv256/$D/$m.lean 2>&1 | cut -c1-${WIDTH:-300}
done
