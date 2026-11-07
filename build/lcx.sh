#!/bin/bash
# lcx.sh TAG FILE [lean opts]: TAG selects the Extracted (X-<tag>/Extracted.olean); FILE absolute. TAG=Extracted FILE=Extracted builds it.
R=/srv/fv-uint256-wI6; FW=/srv/janus-ops/jcache-shared/v1/framework/bf13d15aa4159a3c45a40e30/.lake/build/lib/lean
tag=$1; f=$2; shift; shift
case $tag in aut) ex=ex-arm64-UnmarshalText;; auj) ex=ex-arm64-UnmarshalJSON;; *) ex=ex-arm64-$tag;; esac
O=$R/build/ol; X=$R/build/X-$tag; mkdir -p $X
if [ "$f" = "Extracted" ]; then cd $R/build/$ex; LEAN_PATH=$FW timeout 900 /root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean Extracted.lean -o $X/Extracted.olean; exit; fi
cd $R/lean
rel=$(realpath --relative-to=$R/lean $f); mod=${rel%.lean}; mkdir -p $O/$(dirname $mod)
LEAN_NUM_THREADS=8 LEAN_PATH=$FW:$X:$O timeout 1800 memcap -m 30G /root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean "$@" $rel -o $O/$mod.olean 2>&1 | grep -v "^$"
