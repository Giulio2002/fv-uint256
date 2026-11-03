#!/bin/bash
set -x
export PATH=$PATH:/usr/local/go/bin
export TMPDIR=/srv/fv-uint256-wB-deeprec/tmp LEAN_NUM_THREADS=4 JANUS_JOBS=2
[ -d /srv/janus-fvb-s15 ] || git -C /srv/janus worktree add --detach /srv/janus-fvb-s15 854021d3
cd /srv/janus-fvb-s15 && git log --oneline -1 && CGO_ENABLED=0 go build -o bin/janus ./cmd/janus || exit 1
# consumer copy
mkdir -p /srv/fv-uint256-wB-s15 && cd /srv/fv-uint256-wB-s15
rsync -a --exclude .lake /srv/fv-uint256-wB/lean/ lean/
sed -i 's#/srv/janus-fvb-janus#/srv/janus-fvb-s15#' lean/lakefile.toml
mkdir -p build && ln -sfn /srv/fv-uint256-wB-deeprec/build/harness-amd64 build/harness-amd64 2>/dev/null
cp -r /srv/fv-uint256-wB-deeprec/build/ex-amd64-Float64 build/ 2>/dev/null
J=/srv/janus-fvb-s15/bin/janus
timeout 3000 memcap $J verify build/ex-amd64-Float64 --proof lean/Fv256/Amd64/Float64.lean --proof-root lean --theorem Fv256.Amd64.Float64.correctness > build/vF64.log 2>&1
head -c 400 build/vF64.log
ls -d /root/.cache/janus/v1/framework/*/ | tail -3
touch /srv/fv-uint256-wB-s15/build/setup.done
