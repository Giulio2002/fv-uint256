#!/bin/bash
# lc.sh File.lean [extra lean opts]: compile lean/Fv256/.../File.lean (ABSOLUTE path) against build/ol655
R=/srv/fv-uint256-wB3; FW=/srv/janus-ops/jcache-shared/v1/framework/3f949a7d48d2680d5332b3c9/.lake/build/lib/lean
f=$1; shift
cd $R/lean
rel=$(realpath --relative-to=$R/lean $f)
mod=${rel%.lean}
mkdir -p $R/build/ol655/$(dirname $mod)
LEAN_NUM_THREADS=8 LEAN_PATH=$FW:$R/build/ol655 timeout 900 memcap -m 30G /root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean "$@" $rel -o $R/build/ol655/$mod.olean 2>&1 | grep -v "^$"
