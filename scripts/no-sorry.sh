#!/usr/bin/env bash
# Fails if any .lean file under lean/Fv256 contains the token `sorry`, `admit` or `sorryAx` (outside `--` comments), except files listed in
# WIP-SORRY.txt (format: path<TAB>owner<TAB>note). The allowlist MUST be empty at the final release (RELEASE=1 enforces it).
# Run before every merge:  scripts/no-sorry.sh
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
allow="WIP-SORRY.txt"
[ -f "$allow" ] || { echo "missing $allow"; exit 2; }
declare -A ok=()
nok=0
while IFS=$'\t' read -r path owner note; do
  case "$path" in ''|\#*) continue;; esac
  [ -n "$owner" ] || { echo "FAIL: $allow entry '$path' has no owner"; exit 1; }
  [ -f "$path" ] || { echo "FAIL: $allow lists missing file $path"; exit 1; }
  ok["$path"]=1; nok=$((nok+1))
done < "$allow"
if [ -n "${RELEASE:-}" ] && [ "$nok" -gt 0 ]; then echo "FAIL (RELEASE): $allow is not empty ($nok entries)"; exit 1; fi
fail=0
while IFS= read -r f; do
  # (not `grep -q` in a pipe: with pipefail an early-exiting grep SIGPIPEs sed and the test would falsely say 'no sorry' on big files)
  if [ "$(sed 's/--.*$//' "$f" | grep -cwE 'sorry|admit|sorryAx')" -gt 0 ]; then
    if [ -n "${ok[$f]+x}" ]; then echo "allowed (WIP): $f"; else echo "FAIL: sorry in $f (not in $allow)"; fail=1; fi
  elif [ -n "${ok[$f]+x}" ]; then echo "note: $f is in $allow but no longer contains sorry (remove it)"; fi
done < <(find lean/Fv256 -name '*.lean' | sort)
# no proof may do host IO or depend on host files/environment (the Janus sandbox is read-only: an IO tactic that "works" on a dev machine
# silently takes other branches in the verifier). Forbidden in lean/** (outside .lake): file system, paths, env, processes, streams, clocks-as-input.
iopat='IO\.FS|System\.FilePath|FilePath|pathExists|IO\.getEnv|IO\.Process|IO\.appendFile|\breadFile\b|\bwriteFile\b|IO\.getRandom|IO\.getStd|IO\.sleep|IO\.setStd|\bbuiltin_initialize\b|^[[:space:]]*initialize\b|\bunsafe\b|IO\.Prim|IO\.rand'
while IFS= read -r f; do
  hits="$(sed 's/--.*$//' "$f" | grep -nE "$iopat" | head -3)"
  if [ -n "$hits" ]; then echo "FAIL: IO / host dependence in $f: $(echo "$hits" | head -1 | cut -c1-120)"; fail=1; fi
done < <(find lean -name '*.lean' -not -path '*/.lake/*' | sort)
# second-layer lints (do not rely on literal tokens): (1) source-level: compile-time commands (#eval, run_cmd, run_tac, run_elab, run_meta, #exit,
# initialize, @[init], unsafe), lakefile code-execution settings, and imports parsed by Lean's own header parser (no prelude / import all / foreign roots);
python3 scripts/lint_source.py || fail=1
# (2) Lean-level (RELEASE): every constant defined in an Fv256 module is checked after elaboration for IO types / IO primitives / initializers
# (scripts/check-lean-lint; needs build/harness-*, a janus binary and the janus lake package, as scripts/check-spec-closure).
if [ -n "${RELEASE:-}" ]; then bash scripts/check-generated.sh || fail=1; python3 scripts/check-lean-lint || fail=1; fi
[ $fail = 0 ] && echo "no-sorry: OK" || echo "no-sorry: FAILED"
exit $fail
