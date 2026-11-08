#!/usr/bin/env bash
# fmt-fast.sh MOD...  : compile Fv256.Arm64.<MOD> from the worktree against the kept Format consumer workspace (writes oleans into a private dir)
C=/srv/janus-ops/jcache-csa/v1/consumer/2f82084352791e4b9987b4f4/e18081c9cbdc5af1055cc14d
O=/srv/fv-uint256-csa-aud/fastlib; mkdir -p $O
export LEAN_PATH=$O:$C/janus/.lake/build/lib/lean
L=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
cd /srv/fv-uint256-csa/lean
for m in "$@"; do
  p=Fv256/Arm64/${m//.//}; mkdir -p $O/$(dirname $p)
  rm -f $O/$p.olean $O/$p.ilean; t0=$(date +%s)
  LEAN_NUM_THREADS=8 memcap -m 24G $L -o $O/$p.olean $p.lean 2>&1 | grep -v "warning\|^  \|linter\|^Note" | head -60
  echo "== $m rc=${PIPESTATUS[0]} $(( $(date +%s)-t0 ))s"
done
