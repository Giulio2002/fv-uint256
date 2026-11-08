#!/usr/bin/env bash
# qc.sh FILE [helper-module...]: quick compile of lean/FILE against a cached consumer workspace (QC_C=.../consumer/X/Y/ of a prior janus run of that row; default newest) with helper modules compiled first.
set -u
W=/srv/fv-uint256-csb; J=/srv/janus-ops/jcache-csb/v1
C=${QC_C:-$(ls -dt $J/consumer/*/*/ | head -1)}
F=${QC_F:-$(ls -dt $J/framework/*/ | head -1)}
O=/srv/fv-uint256-csb-aud/scratch/olean-$(basename $C)
mkdir -p $O/Fv256; rsync -a --ignore-existing ${C}own/lib/root/Fv256/ $O/Fv256/; rsync -a --ignore-existing ${C}root/.lake/build/lib/lean/Fv256/ $O/Fv256/
export LEAN_PATH=$O:${C}janus/.lake/build/lib/lean:${F}.lake/build/lib/lean
cd $W/lean
for m in "${@:2}"; do mkdir -p $O/$(dirname $m); lean --root=. $m.lean -o $O/$m.olean || exit 1; done
lean --root=. $1 2>&1 | cut -c1-1500 | awk '/^[^ ].*: (warning|info)/{skip=1} /^[^ ].*: error/{skip=0} !skip' | grep -v '^Note: This linter'; echo QC-DONE
