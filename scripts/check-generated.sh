#!/usr/bin/env bash
# check-generated.sh: the generated-but-committed proof modules (lean/Fv256/{Arm64,Amd64}/TB/*.lean, produced by scripts/gen-tb-intobig*.sh from the IntoBig
# modules) must equal their generator's output. Regenerates into a TEMP copy and diffs: it NEVER writes a tracked file. Exit 1 on drift
# (fix: run `bash scripts/gen-tb-intobig.sh lean; bash scripts/gen-tb-intobig-amd64.sh lean`, review the diff, re-verify ToBig/IntoBig, commit).
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/lean"; cp -a lean/Fv256 "$tmp/lean/Fv256"
fail=0
[ -f lean/Fv256/Arm64/ToBig.lean ] && bash scripts/gen-tb-intobig.sh "$tmp/lean" || true
[ -f lean/Fv256/Amd64/ToBig.lean ] && [ -f lean/Fv256/Amd64/IntoBigT.lean ] && [ -f scripts/gen-tb-intobig-amd64.sh ] && bash scripts/gen-tb-intobig-amd64.sh "$tmp/lean" || true
for isa in Arm64 Amd64; do
  if [ -d "lean/Fv256/$isa/TB" ]; then
    if ! diff -ru "lean/Fv256/$isa/TB" "$tmp/lean/Fv256/$isa/TB" >"$tmp/diff-$isa" 2>&1; then
      echo "check-generated: FAIL: lean/Fv256/$isa/TB is stale against its generator (the committed file differs from the generator output):"; head -30 "$tmp/diff-$isa"; fail=1
    fi
  fi
done
[ $fail = 0 ] && echo "check-generated: OK (TB modules equal their generator output)"
exit $fail
