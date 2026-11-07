#!/bin/bash
cd /srv/fv-uint256-wJ
until [ "$(wc -l < logs/v77.done)" = "4" ] || ! kill -0 3862463 2>/dev/null; do sleep 30; done
cat logs/v77.done; ls -l --time-style=+%T logs/v77_*.log
