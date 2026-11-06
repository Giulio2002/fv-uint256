#!/bin/bash
# lcx.sh TAG FILE: TAG selects the Extracted (X-<tag>/Extracted.olean); FILE absolute
R=/srv/fv-uint256-wJ; FW=/srv/janus-ops/jcache-shared/v1/framework/1c5739cd9f1ec4026a97b4a2/.lake/build/lib/lean
tag=$1; f=$2; shift; shift
case $tag in mm) ex=ex-arm64-MulMod;; rm) ex=ex-arm64-MulModWithReciprocal;; am) ex=ex-amd64-MulMod;; ar) ex=ex-amd64-MulModWithReciprocal;; fd) ex=ex-amd64-FromDecimal;; mfd) ex=ex-amd64-MustFromDecimal;; ut) ex=ex-amd64-UnmarshalText;; uj) ex=ex-amd64-UnmarshalJSON;; sc) ex=ex-amd64-Scan;; aut) ex=ex-arm64-UnmarshalText;; auj) ex=ex-arm64-UnmarshalJSON;; asc) ex=ex-arm64-Scan;; esac
O=$R/build/ol77; X=$R/build/X-$tag; mkdir -p $X
if [ "$f" = "Extracted" ]; then cd $R/build/$ex; LEAN_PATH=$FW timeout 900 /root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean Extracted.lean -o $X/Extracted.olean; exit; fi
cd $R/lean
rel=$(realpath --relative-to=$R/lean $f); mod=${rel%.lean}; mkdir -p $O/$(dirname $mod)
LEAN_NUM_THREADS=8 LEAN_PATH=$FW:$X:$O timeout 1800 memcap -m 30G /root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean "$@" $rel -o $O/$mod.olean 2>&1 | grep -v "^$"
