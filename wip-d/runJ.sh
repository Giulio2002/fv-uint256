#!/usr/bin/env bash
# usage: runJ.sh Module  -- compile one Float64 piece in kept workspace under heavy-run, timed
m=$1
cat > /srv/fv-uint256-wd/wip-d/exp/runJ.$m.inner.sh <<IN
#!/usr/bin/env bash
s=\$(date +%s)
WIDTH=400 /srv/fv-uint256-wd/wip-d/wscase.sh arm64 Float64 $m > /srv/fv-uint256-wd/wip-d/exp/$m.out 2>&1
echo "time=\$((\$(date +%s)-s))s" >> /srv/fv-uint256-wd/wip-d/exp/$m.out
IN
chmod +x /srv/fv-uint256-wd/wip-d/exp/runJ.$m.inner.sh
HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- /srv/fv-uint256-wd/wip-d/exp/runJ.$m.inner.sh
