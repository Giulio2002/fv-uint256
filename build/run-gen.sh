#!/bin/bash
# compile the generalized udivrem chain C..L in order, stop at first failure. log: build/gen.log, progress: build/gen.step
cd /srv/fv-uint256-wB
export PATH=$PATH:/usr/local/go/bin
: > build/gen.log
for f in ${GEN_FILES:-UdivremC UdivremD UdivremE UdivremF UdivremG UdivremH UdivremI UdivremJ UdivremK UdivremL}; do
  echo "$f" > build/gen.step
  s=$(date +%s)
  rm -f build/olean-d/Fv256/Amd64/$f.olean
  DEPS="$f" timeout 3000 memcap tools-local/lean1d.sh amd64 Div UdivremA >> build/gen.log 2>&1
  echo "== $f elapsed $(( $(date +%s) - s )) s" >> build/gen.log
  if [ ! -f build/olean-d/Fv256/Amd64/$f.olean ]; then echo "FAILED $f" >> build/gen.log; break; fi
done
touch build/gen.done
