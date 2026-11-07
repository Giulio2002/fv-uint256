#!/usr/bin/env bash
# rowbatch.sh FN... : rowrun each row in turn; summary lines in /srv/fv-uint256-csb-aud/rb.log
for fn in "$@"; do echo "##### $fn $(date +%H:%M)" >> /srv/fv-uint256-csb-aud/rb.log; /srv/fv-uint256-csb/scripts/rowrun.sh $fn >> /srv/fv-uint256-csb-aud/rb.log 2>&1; done
echo BATCHEND >> /srv/fv-uint256-csb-aud/rb.log
