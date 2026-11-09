#!/usr/bin/env bash
# check-generated.sh: every generated-but-committed proof module must equal its generator's output. Runs EVERY scripts/gen-*.sh (they take LEAN_DIR)
# on a TEMP copy of lean/Fv256 (TB generators first, then the FM ones that read them) and diffs the whole tree: it NEVER writes a tracked file.
# Exit 1 on drift or on a generator that fails. Fix: run the generators in place (same order as GEN_ORDER below), review the diff, re-verify the rows
# whose import chain changed (ToBig, Format, IntoBig), commit.
# scripts/gen-*.py (gen-amain, gen-amfdwit, gen-mfdwit) are historical one-shot generators with hard-coded paths into another worktree
# (/srv/fv-uint256-wJ): they cannot be re-run here, their outputs are ordinary committed sources.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
GEN_ORDER="gen-tb-intobig gen-tb-intobig-amd64 gen-fm-hex-arm64 gen-fm-hex-amd64 gen-fm-intobig-arm64 gen-fm-intobig-amd64"
fail=0
# layout: after scripts/restructure.py the generators run unchanged on a LEGACY VIEW of the Spec/ + Proofs/ modules and their output is split back
# (scripts/gen-layout.py); the generated TB/FM modules live in lean/Fv256/{Spec,Proofs}/{Arm64,Amd64}/{TB,FM}.
if [ -d lean/Fv256/Proofs ] && [ -f scripts/layout-map.json ]; then
  for g in scripts/gen-*.sh; do b="$(basename "$g" .sh)"; case " $GEN_ORDER " in *" $b "*) ;; *) echo "check-generated: FAIL: $g is not listed in GEN_ORDER of scripts/check-generated.sh"; fail=1;; esac; done
  python3 scripts/gen-layout.py check --order "$GEN_ORDER" lean || fail=1
  [ $fail = 0 ] && echo "check-generated: OK (all $(echo $GEN_ORDER | wc -w) generators reproduce the committed modules, via the legacy view)"
  exit $fail
fi
# every shell generator in the repo must be in GEN_ORDER (a new generator must be added here)
for g in scripts/gen-*.sh; do b="$(basename "$g" .sh)"; case " $GEN_ORDER " in *" $b "*) ;; *) echo "check-generated: FAIL: $g is not listed in GEN_ORDER of scripts/check-generated.sh"; fail=1;; esac; done
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/lean"; cp -a lean/Fv256 "$tmp/lean/Fv256"
for b in $GEN_ORDER; do
  bash "scripts/$b.sh" "$tmp/lean" >"$tmp/gen-$b.log" 2>&1 || { echo "check-generated: FAIL: scripts/$b.sh failed on a temp copy:"; tail -5 "$tmp/gen-$b.log"; fail=1; }
done
if ! diff -ru lean/Fv256 "$tmp/lean/Fv256" >"$tmp/diff" 2>&1; then
  echo "check-generated: FAIL: generated modules differ from their generators' output (committed file vs generator):"; head -40 "$tmp/diff"; fail=1
fi
[ $fail = 0 ] && echo "check-generated: OK (all $(echo $GEN_ORDER | wc -w) generators reproduce the committed modules)"
exit $fail
