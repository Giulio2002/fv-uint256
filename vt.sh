#!/bin/bash
# usage: vt.sh FN ISA TAG THMS...   verify FN on ISA from a snapshot with janus 77fb30cc
fn=$1; isa=$2; tag=$3; shift 3
D=$([ $isa = arm64 ] && echo Arm64 || echo Amd64)
R=/srv/fv-uint256-wT
snap=$R/stage-$fn-$isa
rm -rf $snap; mkdir -p $snap/lean
(cd $R/lean && tar cf - --exclude=.lake . ) | tar xf - -C $snap/lean
cp -a $R/lean/.lake $snap/lean/.lake
export LEAN_NUM_THREADS=8 JANUS_JOBS=2 JANUS_CACHE_DIR=/srv/janus-ops/jcache-shared PATH=$PATH:/usr/local/go/bin
J=/srv/janus-fvA-pin77f/bin/janus
cd $R
echo $$ > out/vt-$fn-$isa-$tag.pid
S=$(date +%s)
HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- timeout 7200 memcap -m 40G $J verify build/ex-$isa-$fn --proof $snap/lean/Fv256/$D/$fn.lean --proof-root $snap/lean --full-errors $EXTRA "$@" > out/vt-$fn-$isa-$tag.log 2>&1
echo "rc=$? time=$(( $(date +%s)-S ))s" >> out/vt-$fn-$isa-$tag.log
echo ENDMARK >> out/vt-$fn-$isa-$tag.log
