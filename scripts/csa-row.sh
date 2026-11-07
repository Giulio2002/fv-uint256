#!/usr/bin/env bash
# csa-row.sh ISA FN [audit|full]  : extract + janus verify in the scratch tree /srv/fv-uint256-csa-aud (pinned janus-up3 8615b09c)
# env STUB=1 sorries `correctness` (scratch tree only); KEEP=1 adds --keep-workspace
set -u
isa=$1; fn=$2; mode=${3:-audit}
W=/srv/fv-uint256-csa; A=/srv/fv-uint256-csa-aud; JANUS=/srv/janus-up3/bin/janus
export LEAN_NUM_THREADS=8 JANUS_JOBS=2 JANUS_CACHE_DIR=/srv/janus-ops/jcache-csa
rsync -a --delete $W/lean/Fv256/ $A/lean/Fv256/ ; cp $W/lean/Fv256.lean $A/lean/Fv256.lean
cd $A
. $W/scripts/contract-flags.sh
case $isa in arm64) dir=Arm64;; amd64) dir=Amd64;; esac
if grep -q "^| \`(\*uint256.Int).$fn\`" $W/COVERAGE.md; then full="github.com/holiman/uint256.(*Int).$fn"; else full="github.com/holiman/uint256.$fn"; fi
pf=$fn; if [ -f lean/Fv256/$dir/${fn}Main.lean ] && grep -q "theorem correctness" lean/Fv256/$dir/${fn}Main.lean; then pf=${fn}Main; fi
[ -n "${STUB:-}" ] && python3 $W/scripts/stub-correctness.py lean/Fv256/$dir/$pf.lean
mkdir -p build; out=build/ex-$isa-$fn
if [ ! -d $out ]; then
$JANUS extract /srv/fv-uint256-wrun/build/harness-$isa "$full" $out $(contract_flags $fn) >build/log-$isa-$fn 2>&1 || { echo "EXTRACT-FAIL $isa $fn"; exit 1; }
fi
wt=(); while IFS= read -r w; do [ -n "$w" ] && wt+=(--theorem "$w"); done < <(python3 $W/scripts/witness-theorems.py lean/Fv256/$dir/$pf.lean)
[ $mode = audit ] && export JANUS_STOP_AFTER_AUDIT=1
kw=""; [ -n "${KEEP:-}" ] && kw="--keep-workspace"
t0=$(date +%s)
memcap -m 24G $JANUS verify $out --proof lean/Fv256/$dir/$pf.lean --proof-root lean --janus-root /srv/janus-up3 $kw --theorem Fv256.$dir.$pf.correctness "${wt[@]}" >>build/log-$isa-$fn 2>&1
rc=$?
echo "ENDMARK $isa $fn $mode rc=$rc $(( $(date +%s)-t0 ))s"
