#!/bin/bash
# lc.sh FILE: compile an Extracted-free file (absolute path) into build/ol
R=/srv/fv-uint256-wI6; FW=/srv/janus-ops/jcache-shared/v1/framework/bf13d15aa4159a3c45a40e30/.lake/build/lib/lean
f=$1; shift
cd $R/lean; rel=$(realpath --relative-to=$R/lean $f); mod=${rel%.lean}; mkdir -p $R/build/ol/$(dirname $mod)
LEAN_NUM_THREADS=8 LEAN_PATH=$FW:$R/build/ol timeout 1800 memcap -m 30G /root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean "$@" $rel -o $R/build/ol/$mod.olean 2>&1 | grep -v "^$"
