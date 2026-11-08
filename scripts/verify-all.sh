#!/usr/bin/env bash
# Build the harness for both ISAs, then extract and `janus verify` every function whose COVERAGE.md row says
# `verified` for an ISA. Usage: JANUS=/path/to/janus scripts/verify-all.sh [FN ...]   (default: all verified)
# Env: ROWS=N (rows verified in parallel, default 1; the final run uses 4); MEMCAP (per-row memory cap, default 24G); MAX_LOAD (40) and MIN_MEM_GB (80): admission rules checked before each row starts;
#      HEAVY_PRIORITY (default 0; rows go through /srv/janus-ops/bin/heavy-run when it exists, HEAVY_RUN=0 bypasses); JANUS_CACHE_DIR (default: a FRESH empty dir build/jcache-<stamp>; a non-empty dir is refused unless ALLOW_WARM_CACHE=1);
#      WITNESS (default 1; every witness theorem is verified with correctness, WITNESS=0 disables); WITNESS=1 (also verify Witness.nonvacuous where the proof has it; needs the Janus witness rule), SKIP_HARNESS=1 (reuse build/harness-*, for parallel chunks), PER_FN_TIMEOUT (seconds, default 1800), LEAN_NUM_THREADS (4), JANUS_JOBS (2).
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
JANUS="${JANUS:-janus}"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-8}" JANUS_JOBS="${JANUS_JOBS:-2}"
TMO="${PER_FN_TIMEOUT:-7200}"
WITNESS="${WITNESS:-1}"; NPAR="${ROWS:-1}"; MAX_LOAD="${MAX_LOAD:-40}"; MIN_MEM_GB="${MIN_MEM_GB:-80}"
export MEMCAP="${MEMCAP:-24G}"; export HEAVY_PRIORITY="${HEAVY_PRIORITY:-0}"
command -v memcap >/dev/null || { echo "error: memcap not found (every row must run under a memory cap)" >&2; exit 2; }
MC=memcap
HR=""; if [ "${HEAVY_RUN:-1}" != 0 ] && [ -x /srv/janus-ops/bin/heavy-run ]; then HR=/srv/janus-ops/bin/heavy-run; fi
command -v /usr/bin/time >/dev/null || { echo "error: /usr/bin/time (GNU time) needed for peak RSS" >&2; exit 2; }
# a FRESH cache: a cache built against another pin/extractor can poison kernel replay (see FV-A-HANDOVER fact 2)
if [ -z "${JANUS_CACHE_DIR:-}" ]; then JANUS_CACHE_DIR="$root/build/jcache-$(date +%Y%m%d-%H%M%S)"; fi
mkdir -p "$JANUS_CACHE_DIR"
if [ -n "$(ls -A "$JANUS_CACHE_DIR" 2>/dev/null)" ] && [ -z "${ALLOW_WARM_CACHE:-}" ]; then echo "error: JANUS_CACHE_DIR=$JANUS_CACHE_DIR is not empty: the final run needs a fresh cache (ALLOW_WARM_CACHE=1 to override for a dev run)" >&2; exit 2; fi
export JANUS_CACHE_DIR
echo "verify-all: JANUS=$JANUS ($(sha256sum "$(command -v "$JANUS")" | cut -c1-16)) cache=$JANUS_CACHE_DIR rows-parallel=$NPAR memcap=$MEMCAP witness=$WITNESS"
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

# ---- row jobs -------------------------------------------------------------------------------------------------------------
# One job per (ISA, function). Results go to build/res/<isa>-<fn> as "VERDICT seconds peakRSS_MB". Jobs run up to ROWS at a time.
rm -rf build/res; mkdir -p build/res
declare -a jobs_isa jobs_fn jobs_kind jobs_tag   # kind: row | v3 ; tag: pretty status text for non-run rows
declare -a order_isa order_fn
heavyfirst=" $(grep -v '^#' "$root/scripts/heavy-first.txt" 2>/dev/null | tr '\n' ' ') "
# A row whose per-ISA status is `todo` or `in progress (...)` is reported as MISSING and makes the run FAIL (never skipped silently).
# rows: | `(*uint256.Int).Fn` | owner | arm64 status | amd64 status | ...  (functions: uint256.Fn or (*uint256.Int).Fn)
mapfile -t rows < <(grep -E '^\| `' COVERAGE.md)
fail=0
for row in "${rows[@]}"; do
  sym=$(echo "$row" | cut -d'|' -f2 | tr -d ' `')
  st_arm=$(echo "$row" | cut -d'|' -f4 | tr -d ' '); st_amd=$(echo "$row" | cut -d'|' -f5 | tr -d ' ')
  fn="${sym##*.}"
  [ $# -gt 0 ] && { case " $* " in *" $fn "*) ;; *) continue;; esac; }
  for pair in "arm64:$st_arm" "amd64:$st_amd"; do
    IFS=: read -r isa st <<<"$pair"
    case "$st" in
      verified*|partial*) jobs_isa+=("$isa"); jobs_fn+=("$fn"); jobs_kind+=(row); jobs_tag+=("$sym");;
      todo*|inprogress*|in-progress*) echo "MISSING ($st)" >"build/res/$isa-$fn.pre"; echo "MISSING 0 0" >"build/res/$isa-$fn"; fail=1
         jobs_isa+=("$isa"); jobs_fn+=("$fn"); jobs_kind+=(done); jobs_tag+=("$sym");;
      *) ;;   # n/a, out of scope
    esac
  done
done
# extra proofs about the GOAMD64=v3 build (functions whose default v1 code the Janus model cannot run)
for f in lean/Fv256/Amd64v3/*.lean; do
  [ -e "$f" ] || continue
  fn="$(basename "$f" .lean)"
  [ $# -gt 0 ] && { case " $* " in *" $fn "*) ;; *) continue;; esac; }
  jobs_isa+=(amd64v3); jobs_fn+=("$fn"); jobs_kind+=(v3); jobs_tag+=("$fn")
done

run_job() {   # run_job isa fn kind sym   (runs in a background subshell; never touches shared state besides build/*-$isa-$fn)
  local isa="$1" fn="$2" kind="$3" sym="$4" dir full out cflags pf wt w r t0 rss tf
  t0=$(date +%s); tf="build/time-$isa-$fn"; rm -f "$tf"
  out="build/ex-$isa-$fn"
  if [ "$kind" = v3 ]; then
    if $JANUS extract build/harness-amd64v3 "github.com/holiman/uint256.(*Int).$fn" "$out" >"build/log-$isa-$fn" 2>&1 &&
       $HR timeout "$TMO" /usr/bin/time -f '%M' -o "$tf" $MC -m "$MEMCAP" $JANUS verify "$out" --proof "lean/Fv256/Amd64v3/$fn.lean" --proof-root lean --theorem "Fv256.Amd64v3.$fn.correctness" >>"build/log-$isa-$fn" 2>&1; then r=PASS; else r=FAIL; fi
  else
    case "$isa" in arm64) dir=Arm64;; amd64) dir=Amd64;; esac
    case "$sym" in "(*uint256.Int)."*) full="github.com/holiman/uint256.(*Int).$fn";; *) full="github.com/holiman/uint256.$fn";; esac
    cflags="$(contract_flags "$fn")"
    # a verified row with neither a flags case (contract-flags.sh) nor an entry in noflags.txt is a configuration gap: FAIL, never guess
    if ! contract_known "$fn"; then echo "no contract-flags case for $fn: add the flags of its verified extraction to scripts/contract-flags.sh (or scripts/noflags.txt)" >"build/log-$isa-$fn"; echo "FAIL(no-flags-case) 0 0" >"build/res/$isa-$fn"; return; fi
    # proof module: FnMain.lean, when it exists and holds `theorem correctness`, is the full-spec proof and wins over Fn.lean
    pf="$fn"; if [ -f "lean/Fv256/$dir/${fn}Main.lean" ] && grep -q "theorem correctness" "lean/Fv256/$dir/${fn}Main.lean"; then pf="${fn}Main"; fi
    # every existential witness theorem declared in the module (Witness.nonvacuous, Grow.Witness.nonvacuous, Witness.big, ...): scripts/witness-theorems.py
    wt=(); if [ "$WITNESS" != 0 ]; then while IFS= read -r w; do [ -n "$w" ] && wt+=(--theorem "$w"); done < <(python3 "$root/scripts/witness-theorems.py" "lean/Fv256/$dir/$pf.lean"); fi
    if $JANUS extract "build/harness-$isa" "$full" "$out" $cflags >"build/log-$isa-$fn" 2>&1 &&
       $HR timeout "$TMO" /usr/bin/time -f '%M' -o "$tf" $MC -m "$MEMCAP" $JANUS verify "$out" --proof "lean/Fv256/$dir/$pf.lean" --proof-root lean \
         --theorem "Fv256.$dir.$pf.correctness" "${wt[@]}" >>"build/log-$isa-$fn" 2>&1; then r=PASS; else r=FAIL; fi
    # UP3c: every fv-uint256 row must audit with runFree=false AND refutation=false (a row that claims no run is not a verified function spec): FAIL a row whose reports carry either flag
    if [ "$r" = PASS ] && { grep -rEqs '"(runFree|refutation)": *true' "$out/verified.json" "$out/verified" 2>/dev/null || grep -Eqs 'Non-vacuity: Verified \((run-free|refutation)' "build/log-$isa-$fn"; }; then
      echo "FAIL: the audit reports runFree=true or refutation=true for $isa $fn (every row must be a run-claiming function spec)" >>"build/log-$isa-$fn"; r="FAIL(runFree-or-refutation)"
    fi
  fi
  rss=0; [ -s "$tf" ] && rss=$(( $(tail -1 "$tf" | tr -dc 0-9) / 1024 ))
  echo "$r $(( $(date +%s) - t0 )) $rss ${#wt[@]}" >"build/res/$isa-$fn"
}
admit() {   # load and memory admission rules
  local l m; l=$(cut -d' ' -f1 /proc/loadavg | cut -d. -f1); m=$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo)
  [ "$l" -lt "$MAX_LOAD" ] && [ "$m" -ge "$MIN_MEM_GB" ]
}
# schedule: known-heavy functions first (scripts/heavy-first.txt) so the tail of the run is short
idx=(); for i in "${!jobs_fn[@]}"; do [ "${jobs_kind[$i]}" = done ] && continue; case "$heavyfirst" in *" ${jobs_fn[$i]} "*) idx=("$i" "${idx[@]}");; *) idx+=("$i");; esac; done
# (heavy ones were prepended in reverse; order among them is irrelevant)
declare -a pids
t_start=$(date +%s); lastlaunch=0
for i in "${idx[@]}"; do
  while :; do
    running=$(jobs -rp | wc -l)
    if [ "$running" -lt "$NPAR" ] && [ $(( $(date +%s) - lastlaunch )) -ge "${LAUNCH_GAP:-30}" ] && admit; then break; fi
    sleep 5
  done
  run_job "${jobs_isa[$i]}" "${jobs_fn[$i]}" "${jobs_kind[$i]}" "${jobs_tag[$i]}" &
  lastlaunch=$(date +%s)
done
wait
# ---- summary --------------------------------------------------------------------------------------------------------------
# "== summary ==" lines `ISA Fn VERDICT` are what mark-pin.py reads; the table after "== timing ==" has wall time, peak RSS (largest process) and the witness theorem count per row.
table=""; ttable=""
for i in "${!jobs_fn[@]}"; do
  isa="${jobs_isa[$i]}"; fn="${jobs_fn[$i]}"
  if [ -s "build/res/$isa-$fn" ]; then read -r r s m nw <"build/res/$isa-$fn"; else r="FAIL(no-result)"; s=0; m=0; nw=0; fi
  case "$r" in PASS) ;; *) fail=1;; esac
  table+="$(printf '%-8s %-24s %s' "$isa" "$fn" "$r")"$'\n'
  ttable+="$(printf '%-8s %-24s %-16s %7ss %7s MB  witnesses=%s' "$isa" "$fn" "$r" "$s" "$m" "${nw:-0}")"$'\n'
done
echo "== summary =="; printf '%s' "$table"
echo "== timing (wall seconds, peak RSS of the largest process in the row, witness theorems verified) =="; printf '%s' "$ttable"
echo "== total wall $(( $(date +%s) - t_start )) s, harness hashes OK, cache $JANUS_CACHE_DIR =="
exit $fail
