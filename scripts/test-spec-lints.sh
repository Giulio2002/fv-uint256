#!/usr/bin/env bash
# Regression tests for check-spec-closure's import hygiene (RT-N11 fvside rows A.lean / B.lean): each Spec/ file below MUST make
# `check-spec-closure --structure-only` fail. usage: scripts/test-spec-lints.sh
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"; t="$(mktemp -d "${TMPDIR:-/tmp}/spec-lint-tests.XXXXXX")"; trap 'rm -rf "$t"' EXIT
bad=0
mk() { local d=$1; mkdir -p "$d/lean/Fv256/Spec" "$d/lean/Fv256/Proofs" "$d/scripts"; cp scripts/check-spec-closure scripts/lint_source.py scripts/LintImports.lean "$d/scripts/"; cp lean/lean-toolchain "$d/lean/"; printf 'import Fv256.Spec.Core\n' > "$d/lean/Fv256/Spec.lean"; printf 'namespace Fv256.Spec\ndef core := 1\n' > "$d/lean/Fv256/Spec/Core.lean"; }
case1() { local n=$1 body=$2 d="$t/$1"; mk "$d"; printf '%s\n' "$body" > "$d/lean/Fv256/Spec/Bad.lean"
  out="$(cd "$d" && python3 scripts/check-spec-closure --structure-only 2>&1)"; rc=$?
  if [ $rc -ne 0 ]; then echo "ok   (rejected) $n"; else echo "BAD  $n accepted"; echo "$out" | tail -2; bad=1; fi; }
case1 one-line-import 'import Fv256.Spec.Core import Fv256.Proofs.IOBypass1
namespace Fv256.Spec
def a := 1'
case1 import-all 'import all Fv256.Proofs.IOBypass1
namespace Fv256.Spec
def b := 1'
case1 prelude-import 'prelude
import Fv256.Proofs.X
namespace Fv256.Spec
def c := 1'
case1 comment-then-proofs '/- import Fv256.Spec.Core -/
import Fv256.Proofs.X'
mk "$t/ok"; printf 'import Fv256.Spec.Core\nimport Janus\nnamespace Fv256.Spec\ndef ok := 1\n' > "$t/ok/lean/Fv256/Spec/Good.lean"
(cd "$t/ok" && python3 scripts/check-spec-closure --structure-only >/dev/null 2>&1) && echo "ok   (accepted) control" || { echo "BAD  control rejected"; bad=1; }
[ $bad = 0 ] && echo "test-spec-lints: OK" || echo "test-spec-lints: FAILED"; exit $bad
