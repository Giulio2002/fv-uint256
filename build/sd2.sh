#!/bin/bash
cd /srv/fv-uint256-wh
( time bash build/lc2.sh SDivSum ) > build/sd2.log 2>&1
