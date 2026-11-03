#!/bin/bash
# usage: v.sh ISA FN   verify one function (extracts first if needed). ISA = arm64 | amd64 | amd64v3
# env: FV_ROOT (repo root, default: parent of this script), FV_JANUS (path to the janus binary, default: janus in PATH),
#      FV_CONTRACTS (extra flags for janus extract, e.g. "--contract runtime.newobject")
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4} JANUS_JOBS=${JANUS_JOBS:-2}
FV_ROOT=${FV_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}
J=${FV_JANUS:-janus}
cd "$FV_ROOT" || exit 2
I=$1; F=$2; D=$(echo ${I:0:1}|tr a-z A-Z)${I:1}
case "$F" in NewInt|FromBig|MustFromBig|FromHex|MustFromHex) full="github.com/holiman/uint256.$F";; *) full="github.com/holiman/uint256.(*Int).$F";; esac
. "$FV_ROOT/scripts/contract-flags.sh"
if [ ! -f build/ex-$I-$F/identity.json ]; then $J extract build/harness-$I "$full" build/ex-$I-$F $FV_CONTRACTS $(contract_flags $F) >/dev/null 2>&1; fi
MC=""; command -v memcap >/dev/null && MC=memcap
timeout ${FV_TIMEOUT:-1800} $MC $J verify build/ex-$I-$F --proof lean/Fv256/$D/$F.lean --proof-root lean --theorem Fv256.$D.$F.correctness
