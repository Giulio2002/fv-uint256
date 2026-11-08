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
# N13 (LA1): metaprogramming outside the whitelist; attribute forms; (LA3): header-parsed import forms
expect_fail LA1_AttackA scripts/lint-tests/src/LA1_AttackA_ElabEval.lean 'metaprogramming `elab`'
expect_fail LA1_AttackB scripts/lint-tests/src/LA1_AttackB_ElabConst.lean 'metaprogramming `elab`'
expect_fail LA1_AttackC scripts/lint-tests/src/LA1_AttackC_AttributeInit.lean 'attribute `init`'
expect_fail LA1_Tactic scripts/lint-tests/src/LA1_Tactic.lean 'attribute `tactic`'
expect_fail LA1_Macro scripts/lint-tests/src/LA1_Macro.lean 'metaprogramming `macro`'
expect_fail LA3_TwoImports scripts/lint-tests/src/LA3_TwoImportsOneLine.lean 'imports Evil.Module'
expect_fail LA3_CommentImport scripts/lint-tests/src/LA3_CommentThenImport.lean 'imports Evil.Module'
# (LA2): lakefile srcDir/roots/globs/extra libs/require paths; symlinks; .lean outside lean/ ; whitelist hash drift under RELEASE
tree() {  # dir  -> minimal clean tree
  local d=$1; mkdir -p "$d/lean/Fv256" "$d/scripts"; cp -r scripts/lint_source.py scripts/LintImports.lean scripts/no-sorry.sh "$d/scripts/"; cp lean/lakefile.toml lean/lean-toolchain "$d/lean/"; : > "$d/WIP-SORRY.txt"
  printf 'import Fv256.Other\nnamespace Fv256\ndef x := 1\n' > "$d/lean/Fv256/Clean.lean"
}
expect_rej() {  # name want  (tree already prepared in $t/$1, mutated by the caller)
  out="$(cd "$t/$1" && ${3:-} bash scripts/no-sorry.sh 2>&1)"; rc=$?
  if [ $rc -ne 0 ] && echo "$out" | grep -q -- "$2"; then echo "ok   (rejected) $1"; else echo "BAD  $1 was NOT rejected as expected ($2); rc=$rc"; echo "$out" | tail -3; bad=1; fi
}
tree "$t/LA2_srcDir"; mkdir -p "$t/LA2_srcDir/ext/Fv256"; printf 'import Lean\nrun_cmd pure ()\n' > "$t/LA2_srcDir/ext/Hidden.lean"
printf '\n[[lean_lib]]\nname = "Ext"\nsrcDir = "../ext"\n' >> "$t/LA2_srcDir/lean/lakefile.toml"; expect_rej LA2_srcDir 'lean_lib set must be exactly'
tree "$t/LA2_srcDir2"; sed -i 's/^name = "Fv256"$/name = "Fv256"\nsrcDir = "..\/ext"/' "$t/LA2_srcDir2/lean/lakefile.toml"; expect_rej LA2_srcDir2 'srcDir'
tree "$t/LA2_roots"; sed -i 's/^name = "Fv256"$/name = "Fv256"\nroots = ["Fv256", "X"]\nglobs = ["X.+"]/' "$t/LA2_roots/lean/lakefile.toml"; expect_rej LA2_roots 'roots'
tree "$t/LA2_reqpath"; printf '\n[[require]]\nname = "evil"\npath = "../evil"\n' >> "$t/LA2_reqpath/lean/lakefile.toml"; expect_rej LA2_reqpath 'require `evil` not allowed'
tree "$t/LA2_symlink"; mkdir -p "$t/LA2_symlink/ext"; printf 'import Lean\nrun_cmd pure ()\n' > "$t/LA2_symlink/ext/Hid.lean"; ln -s ../../ext "$t/LA2_symlink/lean/Fv256/Link"; expect_rej LA2_symlink 'symlink'
tree "$t/LA2_outside"; mkdir -p "$t/LA2_outside/ext"; printf 'import Lean\nrun_cmd pure ()\n' > "$t/LA2_outside/ext/Hid.lean"; expect_rej LA2_outside 'outside lean/'
tree "$t/WL_drift"; printf 'import Lean\nnamespace Fv256\nmacro "t1" : tactic => `(tactic| skip)\nend Fv256\n' > "$t/WL_drift/lean/Fv256/Tac.lean"
(cd "$t/WL_drift" && python3 scripts/lint_source.py --update-whitelist >/dev/null && out="$(RELEASE=1 bash scripts/no-sorry.sh 2>&1)" ; true)
if (cd "$t/WL_drift" && bash scripts/no-sorry.sh >/dev/null 2>&1); then echo "ok   (accepted) whitelisted tactic file"; else echo "BAD  whitelisted tactic file rejected"; bad=1; fi
printf -- '-- edited\n' >> "$t/WL_drift/lean/Fv256/Tac.lean"; expect_rej WL_drift 'content changed since whitelisted' 'env RELEASE=1'
tree "$t/WL_new"; cp "$t/WL_drift/scripts/tactic-whitelist.txt" "$t/WL_new/scripts/"; printf 'import Lean\nnamespace Fv256\nmacro "t2" : tactic => `(tactic| skip)\nend Fv256\n' > "$t/WL_new/lean/Fv256/Other2.lean"; expect_rej WL_new 'not listed in scripts/tactic-whitelist.txt'
# a clean tree passes
d="$t/clean"; mkdir -p "$d/lean/Fv256" "$d/scripts"; cp -r scripts/lint_source.py scripts/LintImports.lean scripts/no-sorry.sh "$d/scripts/"; cp lean/lakefile.toml lean/lean-toolchain "$d/lean/"; : > "$d/WIP-SORRY.txt"
printf 'import Fv256.Other\nnamespace Fv256\n/-- #eval run_cmd sorry in a comment is fine -/\ndef x := "run_cmd #eval"\n' > "$d/lean/Fv256/Clean.lean"
if (cd "$d" && bash scripts/no-sorry.sh >/dev/null 2>&1); then echo "ok   (accepted) clean"; else echo "BAD  clean tree rejected"; (cd "$d" && bash scripts/no-sorry.sh 2>&1 | tail -3); bad=1; fi
# Lean-level
ws="${SPEC_WS:-build/spec-ws}"
if [ -d "$ws/tools" ]; then
  cp scripts/SvyTools.lean "$ws/tools/SvyTools.lean"; (cd "$ws" && lake build SvyTools >/dev/null 2>&1)
  for c in IoOpen IoControl ExecElab ExecEval; do cp scripts/lint-tests/lean/$c.lean "$ws/lt-$c.lean"; done
  o="$(cd "$ws" && lake env lean lt-IoOpen.lean 2>&1)"
  for w in readsFile viaEIO Badcmd initX; do echo "$o" | grep -q "@@IO .*$w" && echo "ok   (flagged) lean-level $w" || { echo "BAD  lean-level did not flag $w"; bad=1; }; done
  o="$(cd "$ws" && lake env lean lt-IoControl.lean 2>&1)"; echo "$o" | grep -q '@@IO ' && { echo "BAD  control flagged"; echo "$o" | grep '@@IO ' | head -3; bad=1; } || echo "ok   (clean) lean-level control"
  for c in ExecElab ExecEval; do o="$(cd "$ws" && lake env lean lt-$c.lean 2>&1)"; echo "$o" | grep -q '@@IO .*value-references-exec' && echo "ok   (flagged) lean-level $c" || { echo "BAD  lean-level did not flag $c"; bad=1; }; done
  rm -f "$ws"/lt-*.lean
else echo "BAD  no survey workspace $ws (run scripts/check-lean-lint first)"; bad=1; fi
[ $bad = 0 ] && echo "test-lints: OK" || echo "test-lints: FAILED"; exit $bad
