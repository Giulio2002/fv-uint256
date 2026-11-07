#!/usr/bin/env bash
export OVERLAY=/srv/fv-uint256-wd/wip-d/ovl
for f in ISDiv ISMod; do
  J=/srv/janus-wd-pin/bin/janus; export PATH=$PATH:/usr/local/go/bin
  [ -d /srv/fv-uint256-wd/build/ex-amd64-$f ] || $J extract /srv/fv-uint256-wd/build/harness-amd64 "github.com/holiman/uint256.(*Int).$f" /srv/fv-uint256-wd/build/ex-amd64-$f >/dev/null 2>&1
  /srv/fv-uint256-wd/wip-d/ver.sh amd64 $f
done
touch /srv/fv-uint256-wd/wip-d/b22.done
