#!/usr/bin/env bash
# qc.sh FN [mod-path-under-Fv256/Amd64]  quick single-file compile of lean/Fv256/Amd64/FN.lean against the cached consumer workspace of the audit tree (needs one prior janus run for FN; ./qc.sh builds helper oleans first)
set -u
W=/srv/fv-uint256-csb; C=$(ls -d /srv/janus-ops/jcache-csb/v1/consumer/*/*/ | head -1); F=$(ls -d /srv/janus-ops/jcache-csb/v1/framework/*/ | head -1)
O=/srv/fv-uint256-csb-aud/scratch/olean
export LEAN_PATH=$O:${C}janus/.lake/build/lib/lean:${C}root/.lake/build/lib/lean:${F}.lake/build/lib/lean
rsync -a --ignore-existing ${C}root/.lake/build/lib/lean/Fv256/ $O/Fv256/
cd $W/lean
for m in "${@:2}"; do mkdir -p $O/$(dirname $m); lean --root=. $m.lean -o $O/$m.olean || exit 1; done
f=${1}; lean --root=. $f 2>&1 | cut -c1-1500 | awk '/^[^ ].*: (warning|info)/{skip=1} /^[^ ].*: error/{skip=0} !skip' | grep -v '^Note: This linter' ; echo QC-DONE
