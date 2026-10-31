#!/usr/bin/env bash
# Build the harness for both ISAs, then extract and `janus verify` every function whose COVERAGE.md row says
# `verified` for an ISA. Usage: JANUS=/path/to/janus scripts/verify-all.sh [FN ...]   (default: all verified)
# Env: PER_FN_TIMEOUT (seconds, default 1800), LEAN_NUM_THREADS (4), JANUS_JOBS (2).
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
JANUS="${JANUS:-janus}"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}" JANUS_JOBS="${JANUS_JOBS:-2}"
TMO="${PER_FN_TIMEOUT:-1800}"
MC=""; command -v memcap >/dev/null && MC=memcap
mkdir -p build
for a in arm64 amd64; do
  (cd go && GOTOOLCHAIN=go1.26.0 CGO_ENABLED=0 GOOS=linux GOARCH=$a go build -trimpath -buildvcs=false -o ../build/harness-$a ./cmd/harness) || { echo "harness build failed ($a)"; exit 2; }
done
(cd go && GOTOOLCHAIN=go1.26.0 GOAMD64=v3 CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build -trimpath -buildvcs=false -o ../build/harness-amd64v3 ./cmd/harness) || { echo "harness build failed (amd64 v3)"; exit 2; }
# rows: | `(*uint256.Int).Fn` | arm64 status | amd64 status | ...  (functions: uint256.Fn or (*uint256.Int).Fn)
mapfile -t rows < <(grep -E '^\| `' COVERAGE.md)
fail=0; table=""
for row in "${rows[@]}"; do
  sym=$(echo "$row" | cut -d'|' -f2 | tr -d ' `')
  st_arm=$(echo "$row" | cut -d'|' -f3 | tr -d ' '); st_amd=$(echo "$row" | cut -d'|' -f4 | tr -d ' ')
  fn="${sym##*.}"
  [ $# -gt 0 ] && { case " $* " in *" $fn "*) ;; *) continue;; esac; }
  case "$sym" in "(*uint256.Int)."*) full="github.com/holiman/uint256.(*Int).$fn";; *) full="github.com/holiman/uint256.$fn";; esac
  for pair in "arm64:$st_arm:Arm64" "amd64:$st_amd:Amd64"; do
    IFS=: read -r isa st dir <<<"$pair"
    [ "$st" = verified ] || continue
    out="build/ex-$isa-$fn"
    if $JANUS extract "build/harness-$isa" "$full" "$out" >"build/log-$isa-$fn" 2>&1 &&
       timeout "$TMO" $MC $JANUS verify "$out" --proof "lean/Fv256/$dir/$fn.lean" --proof-root lean \
         --theorem "Fv256.$dir.$fn.correctness" >>"build/log-$isa-$fn" 2>&1; then r=PASS; else r=FAIL; fail=1; fi
    table+="$(printf '%-8s %-24s %s' "$isa" "$fn" "$r")"$'\n'
  done
done
# extra proofs about the GOAMD64=v3 build (functions whose default v1 code the Janus model cannot run)
for f in lean/Fv256/Amd64v3/*.lean; do
  [ -e "$f" ] || continue
  fn="$(basename "$f" .lean)"
  [ $# -gt 0 ] && { case " $* " in *" $fn "*) ;; *) continue;; esac; }
  out="build/ex-amd64v3-$fn"
  if $JANUS extract build/harness-amd64v3 "github.com/holiman/uint256.(*Int).$fn" "$out" >"build/log-amd64v3-$fn" 2>&1 &&
     timeout "$TMO" $MC $JANUS verify "$out" --proof "$f" --proof-root lean --theorem "Fv256.Amd64v3.$fn.correctness" >>"build/log-amd64v3-$fn" 2>&1; then r=PASS; else r=FAIL; fail=1; fi
  table+="$(printf '%-8s %-24s %s' amd64v3 "$fn" "$r")"$'\n'
done
echo "== summary =="; printf '%s' "$table"
exit $fail
