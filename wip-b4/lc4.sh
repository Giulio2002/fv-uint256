#!/bin/bash
# lc4.sh lean/Fv256/File.lean : compile into wip-b4/ol (core only)
R=/srv/fv-uint256-wBm; O=$R/wip-b4/ol
f=$1; shift
cd $R/lean
mod=$(echo ${f%.lean} | sed 's#^lean/##; s#^\./##')
mkdir -p $O/$(dirname $mod)
LEAN_NUM_THREADS=8 LEAN_PATH=$O timeout 900 memcap -m 16G /root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean "$@" $mod.lean -o $O/$mod.olean 2>&1 | grep -v "^$"
