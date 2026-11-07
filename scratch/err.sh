#!/bin/bash
# err.sh: lean-check FormatNil, print errors and sorries only (short)
/srv/fv-uint256-wfn/scratch/lt.sh "$@" 2>&1 | awk '/error|sorry|ENDMARK/{print; c=12} c>0&&!/error|sorry|ENDMARK/{print; c--}' | cut -c1-260 | head -${N:-60}
