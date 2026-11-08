#!/usr/bin/env bash
# Regression tests for the second-layer lints: every case under scripts/lint-tests/ MUST be rejected (the red-team bypass rows of RT-N11 round 11),
# and the control must pass.  usage: scripts/test-lints.sh   (needs lean on PATH; the Lean-level cases need a survey workspace: SPEC_WS, built by
# scripts/spec_survey.py / scripts/check-lean-lint, default build/spec-ws).
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"; t="$(mktemp -d "${TMPDIR:-/tmp}/lint-tests.XXXXXX")"; trap 'rm -rf "$t"' EXIT
bad=0
expect_fail() {  # name file expected-substring
  local n=$1 f=$2 want=$3 d="$t/$1"; mkdir -p "$d/lean/Fv256" "$d/scripts"; cp -r scripts/lint_source.py scripts/LintImports.lean scripts/no-sorry.sh "$d/scripts/"; cp lean/lakefile.toml lean/lean-toolchain "$d/lean/"; : > "$d/WIP-SORRY.txt"
  cp "$f" "$d/lean/Fv256/"; out="$(cd "$d" && bash scripts/no-sorry.sh 2>&1)"; rc=$?
  if [ $rc -ne 0 ] && echo "$out" | grep -q -- "$want"; then echo "ok   (rejected) $n"; else echo "BAD  $n was NOT rejected as expected ($want); rc=$rc"; echo "$out" | tail -3; bad=1; fi
}
expect_fail IOBypass1 scripts/lint-tests/src/IOBypass1.lean 'run_cmd'
expect_fail IOBypass2 scripts/lint-tests/src/IOBypass2.lean 'run_cmd'
expect_fail SorryAlias scripts/lint-tests/src/SorryAlias.lean 'sorry in'
expect_fail ImportAll scripts/lint-tests/src/ImportAll.lean 'modifier'
expect_fail Prelude scripts/lint-tests/src/Prelude.lean 'prelude'
expect_fail ExitHides scripts/lint-tests/src/ExitHides.lean '#exit'
# a clean tree passes
d="$t/clean"; mkdir -p "$d/lean/Fv256" "$d/scripts"; cp -r scripts/lint_source.py scripts/LintImports.lean scripts/no-sorry.sh "$d/scripts/"; cp lean/lakefile.toml lean/lean-toolchain "$d/lean/"; : > "$d/WIP-SORRY.txt"
printf 'import Fv256.Other\nnamespace Fv256\n/-- #eval run_cmd sorry in a comment is fine -/\ndef x := "run_cmd #eval"\n' > "$d/lean/Fv256/Clean.lean"
if (cd "$d" && bash scripts/no-sorry.sh >/dev/null 2>&1); then echo "ok   (accepted) clean"; else echo "BAD  clean tree rejected"; (cd "$d" && bash scripts/no-sorry.sh 2>&1 | tail -3); bad=1; fi
# Lean-level
ws="${SPEC_WS:-build/spec-ws}"
if [ -d "$ws/tools" ]; then
  cp scripts/SvyTools.lean "$ws/tools/SvyTools.lean"; (cd "$ws" && lake build SvyTools >/dev/null 2>&1)
  for c in IoOpen IoControl; do cp scripts/lint-tests/lean/$c.lean "$ws/lt-$c.lean"; done
  o="$(cd "$ws" && lake env lean lt-IoOpen.lean 2>&1)"
  for w in readsFile viaEIO Badcmd initX; do echo "$o" | grep -q "@@IO .*$w" && echo "ok   (flagged) lean-level $w" || { echo "BAD  lean-level did not flag $w"; bad=1; }; done
  o="$(cd "$ws" && lake env lean lt-IoControl.lean 2>&1)"; echo "$o" | grep -q '@@IO ' && { echo "BAD  control flagged"; echo "$o" | grep '@@IO ' | head -3; bad=1; } || echo "ok   (clean) lean-level control"
  rm -f "$ws"/lt-*.lean
else echo "BAD  no survey workspace $ws (run scripts/check-lean-lint first)"; bad=1; fi
[ $bad = 0 ] && echo "test-lints: OK" || echo "test-lints: FAILED"; exit $bad
