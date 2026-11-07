#!/usr/bin/env bash
# Build the harness for both ISAs, then extract and `janus verify` every function whose COVERAGE.md row says
# `verified` for an ISA. Usage: JANUS=/path/to/janus scripts/verify-all.sh [FN ...]   (default: all verified)
# Env: WITNESS=1 (also verify Witness.nonvacuous where the proof has it; needs the Janus witness rule), SKIP_HARNESS=1 (reuse build/harness-*, for parallel chunks), PER_FN_TIMEOUT (seconds, default 1800), LEAN_NUM_THREADS (4), JANUS_JOBS (2).
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
JANUS="${JANUS:-janus}"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}" JANUS_JOBS="${JANUS_JOBS:-2}"
TMO="${PER_FN_TIMEOUT:-1800}"
MC=""; command -v memcap >/dev/null && MC=memcap
mkdir -p build
# Go toolchain: $GO, else `go` on PATH, else /usr/local/go/bin/go (the harness is built with GOTOOLCHAIN=go1.26.0)
GO="${GO:-$(command -v go || true)}"
[ -n "$GO" ] || { [ -x /usr/local/go/bin/go ] && GO=/usr/local/go/bin/go; }
[ -n "$GO" ] && [ -x "$GO" ] || { echo "error: no Go toolchain found: set GO=/path/to/go or put go on PATH (Go >= 1.21; it downloads go1.26.0 itself)"; exit 2; }
# the proofs depend on the pinned Janus revision through lake (lean/lakefile.toml): fetch it once
if [ ! -d lean/.lake/packages/janus ]; then (cd lean && lake update janus) || { echo "lake update janus failed"; exit 2; }; fi
# ToBig's proof imports the IntoBig modules re-targeted at ToBig's extraction (generated, not committed)
[ -f lean/Fv256/Arm64/ToBig.lean ] && bash scripts/gen-tb-intobig.sh lean
# per-function extraction flags (runtime contracts); see scripts/contract-flags.sh
. "$root/scripts/contract-flags.sh"
if [ -z "${SKIP_HARNESS:-}" ]; then
for a in arm64 amd64; do
  (cd go && GOTOOLCHAIN=go1.26.0 CGO_ENABLED=0 GOOS=linux GOARCH=$a "$GO" build -trimpath -buildvcs=false -o ../build/harness-$a ./cmd/harness) || { echo "harness build failed ($a)"; exit 2; }
done
(cd go && GOTOOLCHAIN=go1.26.0 GOAMD64=v3 CGO_ENABLED=0 GOOS=linux GOARCH=amd64 "$GO" build -trimpath -buildvcs=false -o ../build/harness-amd64v3 ./cmd/harness) || { echo "harness build failed (amd64 v3)"; exit 2; }
fi
# the binary under verification is pinned: build/harness-* must hash to scripts/harness.sha256 (checked even with SKIP_HARNESS). FAIL LOUDLY otherwise.
hbad=0
while read -r h name; do
  case "$h" in ''|\#*) continue;; esac
  got="$(sha256sum "build/$name" 2>/dev/null | awk '{print $1}')"
  if [ "$got" != "$h" ]; then
    echo "HARNESS MISMATCH: build/$name has sha256 ${got:-<missing>}, expected $h (scripts/harness.sha256)." >&2
    hbad=1
  fi
done < "$root/scripts/harness.sha256"
if [ "$hbad" != 0 ]; then
  echo "The library programs are tied to the pinned harness layout. Do NOT regenerate libraries or re-verify silently: restore go/, GOTOOLCHAIN=go1.26.0 and the flags in scripts/harness.sha256, or change them deliberately and re-verify everything." >&2
  exit 3
fi
# A row whose per-ISA status is `todo` or `in progress (...)` is reported as MISSING and makes the run FAIL (never skipped silently).
# rows: | `(*uint256.Int).Fn` | owner | arm64 status | amd64 status | ...  (functions: uint256.Fn or (*uint256.Int).Fn)
mapfile -t rows < <(grep -E '^\| `' COVERAGE.md)
fail=0; table=""
for row in "${rows[@]}"; do
  sym=$(echo "$row" | cut -d'|' -f2 | tr -d ' `')
  st_arm=$(echo "$row" | cut -d'|' -f4 | tr -d ' '); st_amd=$(echo "$row" | cut -d'|' -f5 | tr -d ' ')
  fn="${sym##*.}"
  [ $# -gt 0 ] && { case " $* " in *" $fn "*) ;; *) continue;; esac; }
  case "$sym" in "(*uint256.Int)."*) full="github.com/holiman/uint256.(*Int).$fn";; *) full="github.com/holiman/uint256.$fn";; esac
  for pair in "arm64:$st_arm:Arm64" "amd64:$st_amd:Amd64"; do
    IFS=: read -r isa st dir <<<"$pair"
    case "$st" in
      verified*|partial*) ;;
      todo*|inprogress*|in-progress*)   # a function in the coverage target list with no release-grade proof: FAIL, never skip silently
        table+="$(printf '%-8s %-24s %s' "$isa" "$fn" "MISSING ($st)")"$'\n'; fail=1; continue;;
      *) continue;;   # n/a, out of scope
    esac
    out="build/ex-$isa-$fn"
    cflags="$(contract_flags "$fn")"
    # a verified row with neither a flags case (contract-flags.sh) nor an entry in noflags.txt is a configuration gap: FAIL, never guess
    if ! contract_known "$fn"; then echo "no contract-flags case for $fn: add the flags of its verified extraction to scripts/contract-flags.sh (or scripts/noflags.txt)" >"build/log-$isa-$fn"; table+="$(printf '%-8s %-24s %s' "$isa" "$fn" "FAIL (no flags case)")"$'\n'; fail=1; continue; fi
    # proof module: Fn.lean, or FnMain.lean when the main theorem lives there (split proofs)
    # FnMain.lean, when it exists, is the full-spec proof and wins over Fn.lean (which may be an older partial proof)
    pf="$fn"; if [ -f "lean/Fv256/$dir/${fn}Main.lean" ] && grep -q "theorem correctness" "lean/Fv256/$dir/${fn}Main.lean"; then pf="${fn}Main"; fi
    # every existential witness theorem declared in the module (Witness.nonvacuous, Grow.Witness.nonvacuous, Witness.big, ...): scripts/witness-theorems.py
    wt=(); if [ -n "${WITNESS:-}" ]; then while IFS= read -r w; do [ -n "$w" ] && wt+=(--theorem "$w"); done < <(python3 "$root/scripts/witness-theorems.py" "lean/Fv256/$dir/$pf.lean"); fi
    if $JANUS extract "build/harness-$isa" "$full" "$out" $cflags >"build/log-$isa-$fn" 2>&1 &&
       timeout "$TMO" $MC $JANUS verify "$out" --proof "lean/Fv256/$dir/$pf.lean" --proof-root lean \
         --theorem "Fv256.$dir.$pf.correctness" "${wt[@]}" >>"build/log-$isa-$fn" 2>&1; then r=PASS; else r=FAIL; fail=1; fi
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
