#!/bin/bash
export PATH=$PATH:/usr/local/go/bin
cd /srv/fv-uint256-wh
/usr/bin/time -v bash build/lc2.sh DivModLib > build/dl2.out 2>&1
